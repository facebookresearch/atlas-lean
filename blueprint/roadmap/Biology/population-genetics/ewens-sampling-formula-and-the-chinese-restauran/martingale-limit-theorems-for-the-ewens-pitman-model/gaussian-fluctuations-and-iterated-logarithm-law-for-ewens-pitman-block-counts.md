# Gaussian fluctuations and iterated-logarithm law for Ewens–Pitman block counts

**Model.** The Ewens–Pitman (two-parameter Chinese restaurant) partition of $[n]$ with $\alpha \in [0,1)$, $\theta > -\alpha$ is grown sequentially: given $K_n$ blocks of sizes $n_1,\dots,n_{K_n}$, element $n+1$ starts a new block with probability $(\theta + \alpha K_n)/(\theta + n)$ and joins block $j$ with probability $(n_j - \alpha)/(\theta + n)$. The case $\alpha = 0$ is the Ewens sampling formula of population genetics (allelic partition of a neutral sample). Let $K_n$ be the number of blocks and $K_{r,n}$ the number of blocks of size $r$.

**Theorem.** Let $\alpha \in (0,1)$ and $\theta > -\alpha$.

1. *Almost-sure limit.* $K_n/n^\alpha \to S_{\alpha,\theta}$ almost surely, where the $\alpha$-diversity $S_{\alpha,\theta}$ is positive and finite, with the generalized Mittag-Leffler law.
2. *Gaussian fluctuations.* In distribution,

    $$\frac{K_n - n^\alpha S_{\alpha,\theta}}{\sqrt{K_n}} \xrightarrow{\ \mathcal L\ } \mathcal N(0,1).$$

3. *Law of the iterated logarithm.* Almost surely

    $$\limsup_{n\to\infty}\frac{K_n - n^\alpha S_{\alpha,\theta}}{\sqrt{2K_n\log\log n}} = -\liminf_{n\to\infty}\frac{K_n - n^\alpha S_{\alpha,\theta}}{\sqrt{2K_n\log\log n}} = 1.$$

4. *Blocks of a given size.* For every $r \ge 1$, $K_{r,n}/n^\alpha \to p_\alpha(r)S_{\alpha,\theta}$ almost surely, with

    $$p_\alpha(r) = \frac{\alpha(1-\alpha)^{\overline{r-1}}}{r!},$$

    where $x^{\overline m}$ is the rising factorial; $K_{r,n}$ likewise has Gaussian fluctuations of order $\sqrt{K_{r,n}}$ around a martingale-based centering, and an iterated-logarithm law at scale $\sqrt{n^\alpha\log\log n}$.

The fluctuations are random-centered: centering by $n^\alpha S_{\alpha,\theta}$ (rather than a deterministic sequence) removes the non-Gaussian randomness of $S_{\alpha,\theta}$, leaving a mixed-Gaussian error of variance about $K_n$.

## Expansion

The key martingale is $M_n = \frac{\Gamma(\theta+n)}{\Gamma(\theta+\alpha+n)}\Big(K_n + \frac\theta\alpha\Big)$ (up to constants): from the transition rule, $E[K_{n+1} + \theta/\alpha \mid \mathcal F_n] = (K_n + \theta/\alpha)\big(1 + \frac{\alpha}{\theta+n}\big)$, so normalizing by the product $\prod_k (1 + \alpha/(\theta + k)) \asymp n^\alpha$ gives a positive martingale converging almost surely to $S_{\alpha,\theta}$. The increments of $K_n$ are Bernoulli with success probability $\approx \alpha K_n/n$, so the predictable quadratic variation of the martingale tail is asymptotically proportional to $K_n$ (suitably normalized); the central limit theorem and the law of the iterated logarithm for martingales with random normalization (Hall–Heyde type) then give items 2–3. Block counts of fixed size are handled with a vector martingale built from $(K_{1,n},\dots,K_{r,n})$, whose drift matrix is triangular with explicit eigenvalues.

## Sources

- Bernard Bercu and Stefano Favaro, "A martingale approach to Gaussian fluctuations and laws of iterated logarithm for Ewens–Pitman model", *Stochastic Processes and their Applications* 178 (2024), 104493, <https://doi.org/10.1016/j.spa.2024.104493>. Numbering as in the preprint arXiv:2404.07694v2, <https://arxiv.org/abs/2404.07694v2>: Theorems 2.1 (almost-sure limit), 2.3 (Gaussian fluctuations) and 2.4 (iterated logarithm) for $K_n$, and Theorems 3.1, 3.3 and 3.4 for $K_{r,n}$.
