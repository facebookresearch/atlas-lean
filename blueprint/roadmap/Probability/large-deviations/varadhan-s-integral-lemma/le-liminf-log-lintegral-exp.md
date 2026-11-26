# Lower bound in Varadhan's integral lemma

Let $X$ be a topological space with measurable open sets, and let measures $\mu_n$ on $X$ satisfy
the [large deviation principle](../large-deviation-principle/satisfies-ldp.md) with rate function
$I$. Let $F : X \to \mathbb{R}$ be lower semicontinuous (no boundedness is needed). Then, in
$[-\infty, \infty]$,

$$\sup_{x \in X} \big(F(x) - I(x)\big) \le \liminf_{n \to \infty} \frac{1}{n} \log \int e^{nF} \, d\mu_n .$$
