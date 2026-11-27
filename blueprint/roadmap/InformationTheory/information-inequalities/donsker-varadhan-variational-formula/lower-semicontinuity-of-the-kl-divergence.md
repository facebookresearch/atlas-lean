# Lower semicontinuity of the Kullback–Leibler divergence

Let $X$ be a separable metric space with its Borel σ-algebra. If probability measures $\mu_n \to \mu$ and $\nu_n \to \nu$ weakly on $X$, that is $\int g\, d\mu_n \to \int g\, d\mu$ and $\int g\, d\nu_n \to \int g\, d\nu$ for every bounded continuous $g\colon X \to \mathbb{R}$, then

$$\mathrm{KL}(\mu \,\|\, \nu) \le \liminf_{n \to \infty} \mathrm{KL}(\mu_n \,\|\, \nu_n)$$

in $[0, \infty]$. For example, $X$ may be the path space $C([0, T]; \mathbb{R}^d)$ with the uniform norm.

## Proof depends on

- [Donsker–Varadhan variational formula](kl-div-eq-i-sup.md)

## Expansion

A sound expansion has separate pages for:

1. **The variational formula over bounded continuous functions.** $\mathrm{KL}(\mu \,\|\, \nu) = \sup_g \bigl( \int g\, d\mu - \log \int e^g\, d\nu \bigr)$ with $g$ bounded and continuous. Over bounded measurable $g$ this is the Donsker–Varadhan formula. A measurable $g$ with $|g| \le M$ is a limit in $L^1(\mu + \nu)$ of continuous $g_k$ with $|g_k| \le M$, because a finite Borel measure on a metric space is regular, and both integrals pass to the limit.
2. **Lower semicontinuity.** For each bounded continuous $g$, the map $(\mu, \nu) \mapsto \int g\, d\mu - \log \int e^g\, d\nu$ is continuous for weak convergence, and a supremum of continuous functions is lower semicontinuous.

## Sources

- L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of Probability Measures*, Lectures in Mathematics ETH Zürich, Birkhäuser, 2005, Lemma 9.4.3, cited for this step in the proof of Theorem 10 (Appendix B.2) of S. Chen, S. Chewi, J. Li, Y. Li, A. Salim and A. R. Zhang, *Sampling is as easy as learning the score: theory for diffusion models with minimal data assumptions*, ICLR 2023. <https://par.nsf.gov/servlets/purl/10502932>
