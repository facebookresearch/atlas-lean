# f3 of an admixture followed by drift

In a [drift model](drift-model.md) with lineage weights $w$ and drift lengths $\ell$, let $A, B, C$ be populations, $\alpha \in \mathbb{R}$ and $c$ an edge with $w(A, c) = w(B, c) = 0$ and

$$w(C, e) = \alpha\, w(A, e) + (1 - \alpha)\, w(B, e) + [e = c] \qquad \text{for every edge } e$$

(for $0 \le \alpha \le 1$, $C$ is an $\alpha : 1 - \alpha$ mixture of $A$ and $B$ that then drifts along the private edge $c$). Then

$$f_3(C; A, B) = \ell_c - \alpha (1 - \alpha)\, f_2(A, B),$$

for the [f2](f2.md) and [f3](f3.md) statistics of the [population frequencies](freq.md): post-admixture drift can mask the admixture signal.
