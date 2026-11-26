# Union and intersection of octagons

For coherent DBMs $m^+$ and $n^+$, in the notation of [difference-bound matrices and octagons](difference-bound-matrices-and-octagons.md) over $\mathbb{I} = \mathbb{Q}$ or $\mathbb{R}$, let $[m^+ \wedge n^+]_{ij} = \min(m^+_{ij}, n^+_{ij})$ and $[m^+ \vee n^+]_{ij} = \max(m^+_{ij}, n^+_{ij})$.

1. $D^+(m^+ \wedge n^+) = D^+(m^+) \cap D^+(n^+)$.
2. $D^+(m^+ \vee n^+) \supseteq D^+(m^+) \cup D^+(n^+)$.
3. If both octagons are nonempty, then $(m^+)^\bullet \vee (n^+)^\bullet$ is the least coherent DBM, for the pointwise order, whose octagon contains $D^+(m^+) \cup D^+(n^+)$, where $\bullet$ is the [strong closure](strong-closure-is-a-normal-form-for-octagons.md). In particular it is strongly closed.

## Depends on

- [Difference-bound matrices and octagons](difference-bound-matrices-and-octagons.md)
- [Strong closure is a normal form for octagons](strong-closure-is-a-normal-form-for-octagons.md)

## Proof depends on

- [Strong closure is a normal form for octagons](strong-closure-is-a-normal-form-for-octagons.md)

## Sources

- A. Miné, "The octagon abstract domain", *Higher-Order and Symbolic Computation* 19(1):31–100, 2006; preprint arXiv:cs/0703084, <https://arxiv.org/abs/cs/0703084>, Section VI.C, Theorem 7 and the remarks after it.
