# Satisfiability of transformer encoders with hardmax attention is undecidable

Whether a transformer encoder accepts at least one input word is undecidable already for a deliberately weak class: hardmax attention whose scores are ReLU networks applied to a dot product, ReLU combination and output functions, and simple positional embeddings. This remains true when computations use logarithmic precision.

**Setting (Sälzer, Alsmann and Lange).** A *transformer encoder* (TE) $T$ over a finite alphabet $\Sigma$ with $L$ layers consists of a positional embedding $\mathrm{emb} : \Sigma \times \mathbb{N} \to \mathbb{R}^{d_0}$, attention heads $\mathrm{att}_{i,j} = (\mathrm{score}_{i,j}, \mathrm{pool}_{i,j})$, combinations $\mathrm{comb}_i$ and an output function $\mathrm{out}$. On a word $w = a_1 \cdots a_n \in \Sigma^+$, the first vectors are $\mathrm{emb}(a_m, m)$; layer $i$ maps $\vec{x}^{i-1}_1 \cdots \vec{x}^{i-1}_n$ to $\vec{x}^i_1 \cdots \vec{x}^i_n$, where head $j$ at position $m$ outputs $\sum_{m'} \mathrm{norm}(m', s_1, \dots, s_n)\, W \vec{x}^{i-1}_{m'}$ for the scores $s_{m'} = \mathrm{score}_{i,j}(\vec{x}^{i-1}_m, \vec{x}^{i-1}_{m'})$, and $\vec{x}^i_m$ is $\mathrm{comb}_i$ of $\vec{x}^{i-1}_m$ and the head outputs. $T$ *accepts* $w$ if $\mathrm{out}(\vec{x}^L_n) = 1$. The problem $\mathrm{trSat}[\mathcal{T}]$ asks, given $T$ in a class $\mathcal{T}$, whether $T$ accepts some word. The class $\mathcal{T}_{\mathrm{undec}}$ allows positional embeddings $\mathrm{emb}(a_k, 0) = (1, 1, 0, 0, k)$ and $\mathrm{emb}(a_k, i) = (0, 1, i, \sum_{j=0}^{i} j, k)$ for the $k$-th letter $a_k$; scores $N(\langle Q\vec{x}, K\vec{y} \rangle)$ with $Q$, $K$ linear and $N$ a ReLU network; the hardmax normalization, which spreads weight $1/m$ uniformly over the $m$ positions of maximal score; and ReLU networks as combinations and outputs. As an input, a transformer of these classes is given by the rational entries of its matrices $Q$, $K$, $W$ and the rational weights and biases of its ReLU networks. The class $\mathcal{T}_{\mathrm{undec}}^{\log}$ is defined in the same way, except that $T(w)$ is computed in a fixed-width arithmetic with $O(\log \max(|\Sigma|, |w|))$ bits.

**Theorem (Sälzer, Alsmann and Lange).** The problems $\mathrm{trSat}[\mathcal{T}_{\mathrm{undec}}]$ and $\mathrm{trSat}[\mathcal{T}_{\mathrm{undec}}^{\log}]$ are undecidable.

By contrast, the same paper proves satisfiability decidable for TE working in a fixed-width arithmetic independent of the input length, with NEXPTIME-hardness for some such classes and NEXPTIME upper bounds for others.

## Depends on

- [Transformer layers, numeric regimes and decoding conventions](transformer-layers-numeric-regimes-and-decoding-conventions.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces the unbounded octant tiling-word problem: given tiles $S$, horizontal and vertical relations $H, V \subseteq S^2$ and tiles $t_I, t_F$, decide whether some word $t_{0,0} t_{1,0} t_{1,1} t_{2,0} \cdots t_{k,k}$ encodes a tiling of a triangular region that starts with $t_I$, ends with $t_F$ and respects $H$ and $V$; this problem is $\Sigma^0_1$-complete. Two encoder layers recover, from the positional embedding, the row and column of each symbol, and attention heads can attend to positions given by linear functions of the current vector, which lets a third layer compare each symbol with its horizontal and vertical neighbors and a fourth layer collect the results at the last position. So the encoder built from a tiling system accepts exactly the valid encoded tilings. All values stay polynomial in the input length, so logarithmic precision suffices. A good expansion links a page for the undecidability of the octant tiling-word problem.

## Sources

- Marco Sälzer, Eric Alsmann and Martin Lange, *Transformer Encoder Satisfiability: Complexity and Impact on Formal Reasoning*, The Thirteenth International Conference on Learning Representations (ICLR 2025), 2025, https://proceedings.iclr.cc/paper_files/paper/2025/hash/31f7bb23166893956c570d5bf26f4d18-Abstract-Conference.html; the definition of transformer encoders in Section 2 and the two undecidability theorems of Section 4, with the tiling problem in the appendix, read in arXiv:2405.18548v3. Locators in arXiv:2405.18548v3: Theorems 1, 2 and 6.
