# Varadhan's lower bound on an open set

Let $X$ be a topological space with measurable open sets, and let measures $\mu_n$ on $X$ satisfy
the [large deviation principle](../large-deviation-principle/satisfies-ldp.md) with rate function
$I$. Let $F : X \to \mathbb{R}$ be lower semicontinuous and $U \subseteq X$ open. Then, in
$[-\infty, \infty]$,

$$\sup_{x \in U} \big(F(x) - I(x)\big) \le \liminf_{n \to \infty} \frac{1}{n} \log \int_U e^{nF} \, d\mu_n .$$
