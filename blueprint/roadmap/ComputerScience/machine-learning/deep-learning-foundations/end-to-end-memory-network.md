# A read hop in an end-to-end memory network

Store $n\ge1$ memory slots, with an input embedding $m_i\in\mathbb R^d$ and an output embedding $c_i\in\mathbb R^d$ for each slot. From an embedded query $u\in\mathbb R^d$, one hop reads and updates

$$p_i=\frac{\exp(u^\top m_i)}{\sum_j\exp(u^\top m_j)},\qquad o=\sum_i p_i c_i,\qquad u'=u+o.$$

The next hop matches $u'$, not the original query, against its own input memory vectors. The slots can be the same across hops even when their input and output embeddings differ. In this version the update has an identity skip connection; the read is a soft weighted sum, not a selection of the nearest slot.

## Depends on

- [Softmax](../../not-yet-classified/basic/part-06/softmax.md)

## Sources

- Sukhbaatar et al., [*End-To-End Memory Networks*](https://arxiv.org/abs/1503.08895) (NeurIPS 2015), §§2.1–2.2, equations (1)–(4).
