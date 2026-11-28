# Masked multi-head attention

Let the queries be rows of $X$, the source of keys and values be rows of $Y$, and $S_i$ be a **nonempty** set of source positions visible to query $i$. Each of $H\ge1$ heads has its own projections $Q_h=XW_h^Q$, $K_h=YW_h^K$, $V_h=YW_h^V$, with key and query width $d_k>0$. Its output row is

$$O_{h,i}=\sum_{j\in S_i}\frac{\exp(Q_{h,i}K_{h,j}^{\mathsf T}/\sqrt{d_k})}{\sum_{s\in S_i}\exp(Q_{h,i}K_{h,s}^{\mathsf T}/\sqrt{d_k})}\,V_{h,j}.$$

Concatenate heads along the feature axis and project: $O=[O_1|\cdots|O_H]W^O$. Self-attention takes $Y=X$; cross-attention draws $Y$ from another sequence. Restricting the sum before softmax makes masked weights zero without ever taking a softmax over an empty row.

## Depends on

- [Single-head scaled dot-product attention](../../not-yet-classified/basic/part-06/attn.md)
- [Softmax](../../not-yet-classified/basic/part-06/softmax.md)

## Background

- [Attention logits as bilinear forms](../attention-and-low-rank-adaptation/attention-logits-as-bilinear-forms.md)

## Sources

- Vaswani et al., [*Attention Is All You Need*](https://arxiv.org/abs/1706.03762) (NeurIPS 2017), §§3.2.1–3.2.3, equation (1).
