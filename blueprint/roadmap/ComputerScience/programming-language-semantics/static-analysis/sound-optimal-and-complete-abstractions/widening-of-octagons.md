# Widening of octagons

For coherent DBMs $m^+$ and $n^+$, in the notation of [difference-bound matrices and octagons](difference-bound-matrices-and-octagons.md), let

$$[m^+ \mathbin{\nabla} n^+]_{ij} = \begin{cases} m^+_{ij} & \text{if } n^+_{ij} \le m^+_{ij},\\ +\infty & \text{otherwise.}\end{cases}$$

1. $D^+(m^+ \mathbin{\nabla} n^+) \supseteq D^+(m^+) \cup D^+(n^+)$.
2. For every sequence $(n^+_i)_{i \in \mathbb{N}}$ of coherent DBMs, the sequence $m^+_0 = (n^+_0)^\bullet$, $m^+_i = m^+_{i-1} \mathbin{\nabla} (n^+_i)^\bullet$ for $i > 0$, with the [strong closure](strong-closure-is-a-normal-form-for-octagons.md) $\bullet$, which is defined for bounds in $\mathbb{Q}$ or $\mathbb{R}$, is eventually constant.

So $\nabla$ is a widening on octagons. Strongly closing the left argument as well, $m^+_i = (m^+_{i-1} \mathbin{\nabla} (n^+_i)^\bullet)^\bullet$, breaks part 2: there are strictly increasing infinite sequences of this form.

## Depends on

- [Difference-bound matrices and octagons](difference-bound-matrices-and-octagons.md)
- [Strong closure is a normal form for octagons](strong-closure-is-a-normal-form-for-octagons.md)

## Sources

- A. Miné, "The octagon abstract domain", *Proceedings of the Eighth Working Conference on Reverse Engineering (WCRE 2001)*, IEEE, 2001, pp. 310–319, doi:10.1109/WCRE.2001.957836, author copy <https://arxiv.org/abs/cs/0703084>, Section VI.D, the widening operator, Theorem 8, and Figure 10 (an infinite strictly increasing sequence when the left argument is strongly closed).
