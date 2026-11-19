# Multi-head latent attention (MLA)

Multi-head latent attention, introduced in DeepSeek-V2, computes keys and values from one cached
latent vector per token. Let $d$, $n_h$, $d_h$, $d_c$ and $d_c'$ be positive integers and $d_h^R$ a
positive even integer.

Content keys and values: from a hidden state $h_t \in \mathbb{R}^d$, MLA computes
$c^{KV}_t = W^{DKV} h_t \in \mathbb{R}^{d_c}$ and then $k^C_t = W^{UK} c^{KV}_t$ and
$v^C_t = W^{UV} c^{KV}_t$, with $W^{DKV} \in \mathbb{R}^{d_c \times d}$ and
$W^{UK}, W^{UV} \in \mathbb{R}^{d_h n_h \times d_c}$. The content keys and values are thus those
of multi-head attention whose key and value projections are constrained to $W^{UK} W^{DKV}$ and
$W^{UV} W^{DKV}$. These share the factor $W^{DKV}$, so the stacked map from $h_t$ to
$(k^C_t, v^C_t)$ has rank at most $d_c$, and the key map $W^{UK}_i W^{DKV}$ of head $i$ has rank at
most $\min(d_h, d_c)$ (derived).

Queries are compressed separately: $c^Q_t = W^{DQ} h_t \in \mathbb{R}^{d_c'}$ and
$q^C_t = W^{UQ} c^Q_t$, with $W^{DQ} \in \mathbb{R}^{d_c' \times d}$ and
$W^{UQ} \in \mathbb{R}^{d_h n_h \times d_c'}$.

Decoupled rotary position embedding: positions enter through separate components, a positional query
$q^R_{t,i} \in \mathbb{R}^{d_h^R}$ for each head and a single positional key
$k^R_t \in \mathbb{R}^{d_h^R}$ shared by all heads and computed from $h_t$, not from $c^{KV}_t$.
With $W^{QR} \in \mathbb{R}^{d_h^R n_h \times d_c'}$, its row block
$W^{QR}_i \in \mathbb{R}^{d_h^R \times d_c'}$ for head $i$, and
$W^{KR} \in \mathbb{R}^{d_h^R \times d}$, this page reads the paper's $\mathrm{RoPE}(W^{QR} c^Q_t)$
and $\mathrm{RoPE}(W^{KR} h_t)$ as $q^R_{t,i} = R_t W^{QR}_i c^Q_t$ and $k^R_t = R_t W^{KR} h_t$,
where $R_t \in \mathbb{R}^{d_h^R \times d_h^R}$ is the block rotation of the rotary position
embedding page for position $t$, with the same $d_h^R/2$ angles in every head and in the key. Then
$(q^R_{t,i})^{\mathsf{T}} k^R_j = (W^{QR}_i c^Q_t)^{\mathsf{T}} R_{j-t} W^{KR} h_j$. Head $i$ uses
$q_{t,i} = [q^C_{t,i}; q^R_{t,i}]$ and $k_{j,i} = [k^C_{j,i}; k^R_j]$, computes
$o_{t,i} = \sum_{j \le t} \mathrm{softmax}_j\big(q_{t,i}^{\mathsf{T}} k_{j,i} / \sqrt{d_h + d_h^R}\big)\, v^C_{j,i}$,
and the layer outputs $u_t = W^O [o_{t,1}; \dots; o_{t,n_h}]$ with
$W^O \in \mathbb{R}^{d \times d_h n_h}$. Each logit is the sum of a content term
$(q^C_{t,i})^{\mathsf{T}} k^C_{j,i}$ and a positional term $(q^R_{t,i})^{\mathsf{T}} k^R_j$, so
before masking and softmax the logit matrix of one head over $L \ge 1$ positions has rank at most
$\min(d_h + d_h^R, L)$ (derived).

Reassociation (derived; the paper's appendix states it in words): let $W^{UQ}_i \in
\mathbb{R}^{d_h \times d_c'}$ and $W^{UK}_i, W^{UV}_i \in \mathbb{R}^{d_h \times d_c}$ be the row
blocks of head $i$, and $W^O_i \in \mathbb{R}^{d \times d_h}$ the column block of $W^O$ for head
$i$. Then

- $(q^C_{t,i})^{\mathsf{T}} k^C_{j,i} = (c^Q_t)^{\mathsf{T}} \big[(W^{UQ}_i)^{\mathsf{T}}
  W^{UK}_i\big] c^{KV}_j$, where the bracket is a position-independent $d_c' \times d_c$ matrix
  of rank at most $\min(d_h, d_c', d_c)$;
- $u_t = \sum_i W^O_i o_{t,i} = \sum_i \big(W^O_i W^{UV}_i\big) \sum_{j \le t} a^{(i)}_{tj}
  c^{KV}_j$, where the $a^{(i)}_{tj}$ are the softmax weights of head $i$ and
  $W^O_i W^{UV}_i \in \mathbb{R}^{d \times d_c}$.

Both identities use only the associativity of matrix multiplication and the linearity of the
weighted sum. Whether forming these products saves work depends on the dimensions and the
implementation; in DeepSeek-V2, $d_c' = 1536$ exceeds $d_h = 128$, and no efficiency claim is
made here.

Why the positional part is separate (derived): if rotations
$R_t, R_j \in \mathbb{R}^{d_h \times d_h}$ (with $d_h$ even) were applied to the content queries and
keys, the content logit would read
$(c^Q_t)^{\mathsf{T}} (W^{UQ}_i)^{\mathsf{T}} R_{j-t} W^{UK}_i c^{KV}_j$, whose middle matrix
depends on the offset $j - t$. For generic weights and angles it changes with the offset, so no
single position-independent product could be formed once for all positions.

Cache: per token and per layer, MLA caches $c^{KV}_t$ and $k^R_t$, that is $d_c + d_h^R$
numbers, whereas standard multi-head attention caches all keys and values, $2 n_h d_h$ numbers.
In DeepSeek-V2's configuration ($n_h = d_h = 128$, $d_c = 512$, $d_h^R = 64$) this is $576$
against $32768$ elements per token and layer; these are element counts, not bytes or latency.

The rank bounds describe this parameterization of the attention layer. This page makes no claim
about approximating or compressing a trained multi-head attention layer, and "low rank" refers
to the content key and value maps only: the positional key is a separate map.

## Informally uses

- [Rank of a product of matrices](../../../LinearAlgebra/linear-maps-and-duality/rank-of-a-product.md):
  mathematical prerequisite, the rank bounds through the shared factor and for the absorbed
  per-head matrix.
- [Attention logits as bilinear forms](attention-logits-as-bilinear-forms.md): builds on, since
  MLA changes how the keys and values of multi-head attention are produced.
- [Rotary position embedding (RoPE)](rotary-position-embedding.md): builds on, through the
  decoupled positional queries and key.

## Sources

- DeepSeek-AI, "DeepSeek-V2: A Strong, Economical, and Efficient Mixture-of-Experts Language Model", arXiv:2405.04434 (version 5), Section 2.1.1 (multi-head attention and its cache), Section 2.1.2, equations (9)–(13), Section 2.1.3, equations (14)–(19), Section 2.1.4 and Table 1, Section 3.1.2 (model hyper-parameters), and Appendix C, equations (37)–(47).
