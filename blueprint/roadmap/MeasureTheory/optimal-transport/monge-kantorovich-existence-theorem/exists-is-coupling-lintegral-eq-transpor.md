# Optimal couplings exist for the Wasserstein cost

Let $X$ be a Polish extended metric space with its Borel σ-algebra and $p \in \mathbb{R}$. For all
probability measures $\mu, \nu$ on $X$ there is a coupling $\pi$ of $\mu$ and $\nu$ with

$$\int d(x, y)^p \, d\pi(x, y) = \inf_{\pi'} \int d(x, y)^p \, d\pi'(x, y),$$

so the infimum defining the [Wasserstein distance](../wasserstein-distances/wasserstein.md) is
attained. It is the [existence theorem](exists-is-coupling-forall-lintegral-le.md) for the continuous
cost $d^p$.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Theorem 4.1 and Chapter 6 (optimal couplings in the proof that $W_p$ is a distance).
