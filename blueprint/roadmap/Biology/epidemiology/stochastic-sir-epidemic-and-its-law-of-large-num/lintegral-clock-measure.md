# Iterated integrals of a measurable function against the clock-configuration law

Let $\mathbb{P}$ be the [clock-configuration law](clock-measure.md) on [clock configurations](clock-config.md)
$((r_1, r_2), (u_1, u_2))$, with $r_1, r_2 \in \mathbb{R}$ and
$u_1, u_2 : \mathbb{N} \to \mathbb{R}$: under $\mathbb{P}$ the residual clocks $r_1$, $r_2$ and all
the interarrival times $u_1(n)$, $u_2(n)$ are independent with the
[rate-$1$ exponential law](../../../Probability/distributions/continuous/exponential-distribution/README.md)
$\operatorname{Exp}(1)$. Let $\nu = \operatorname{Exp}(1)^{\otimes \mathbb{N}}$ be the law of an
i.i.d. sequence of such variables. For every measurable function $G$ from clock configurations to
$[0, \infty]$,

$$
\int G \, d\mathbb{P} = \int \int \int \int G\bigl((r_1, r_2), (u_1, u_2)\bigr)
\, d\nu(u_2) \, d\nu(u_1) \, d\operatorname{Exp}(1)(r_2) \, d\operatorname{Exp}(1)(r_1),
$$

integrating first over $u_2$, then over $u_1$, $r_2$ and $r_1$; all the integrals are lower Lebesgue
integrals with values in $[0, \infty]$.
