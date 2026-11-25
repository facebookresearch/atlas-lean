# Varadhan's upper bound on a closed set

Let $X$ be a topological space with measurable open sets, and let measures $\mu_n$ on $X$ satisfy
the [large deviation principle](../large-deviation-principle/satisfies-ldp.md) with a rate
function $I$, not necessarily good. Let $F : X \to \mathbb{R}$ be continuous with $|F| \le C$ and
let $K \subseteq X$ be closed. Then, in $[-\infty, \infty]$,

$$\limsup_{n \to \infty} \frac{1}{n} \log \int_K e^{nF} \, d\mu_n \le \sup_{x \in K} \big(F(x) - I(x)\big).$$
