# Likelihood-ratio optimality of the discriminative reconstruction hinge loss

**Setting (non-B DNA as novelty detection).** Let $x$ be a window of nanopore translocation times, $y \in \{0, 1\}$ the absence or presence of a non-B DNA structure, and $s \in \{0, 1\}$ the absence or presence of a non-B sequence motif, with joint law $p(x, y, s)$. B-DNA training data $X^B$ are drawn from $p(x \mid y = 0, s = 0)$. Motif-containing windows $X^N$ are drawn from $p(x \mid s = 1)$, a mixture of structured ($y = 1$) and unstructured ($y = 0$) windows. The task is to tell $y = 1$ from $y = 0$ inside $X^N$.

**Loss.** With an encoder $F_\theta$, decoder $G_\phi$, reconstruction loss $d \ge 0$, margin $\delta > 0$, weight $\omega > 0$ and a goodness-of-fit regularizer $T$ applied to the encoded B-DNA minibatch, the discriminative autoencoder minimizes

$$\frac{1}{n_B} \sum_{i=1}^{n_B} d\bigl(x_i, G_\phi(F_\theta(x_i))\bigr) + \frac{\omega}{n_N} \sum_{i=1}^{n_N} \max\bigl(0, \delta - d(z_i, G_\phi(F_\theta(z_i)))\bigr) \pm \lambda\, T\bigl(\{F_\theta(x_i)\}\bigr),$$

with $x_i \in X^B$ and $z_i \in X^N$. B-DNA should reconstruct well, motif windows are pushed beyond the margin, and the regularizer makes the encoded B-DNA close to Gaussian.

**Proposition.** Let $K(x) = \delta^{-1} d(x, G_\phi(F_\theta(x)))$ and let

$$J(K) = \mathbb{E}\bigl[\delta K(x)\bigr] + \omega\, \mathbb{E}\bigl[\max(0, \delta - \delta K(x))\bigr]$$

be the population version of the first two terms, the first expectation under $p(x \mid y = 0, s = 0)$ and the second under $p(x \mid s = 1)$. The minimizer $K^\star$ is the likelihood-ratio rule

$$K^\star(x) = \begin{cases} 0 & \text{if } c\, p(x, s = 1) \le p(x, y = 0, s = 0), \\ 1 & \text{if } c\, p(x, s = 1) > p(x, y = 0, s = 0), \end{cases} \qquad c = \frac{\omega\, p(y = 0, s = 0)}{p(s = 1)} .$$

Moreover, if $(1 + c)\, p(x, y = 0, s = 1) < \tfrac12\, p(x, y = 0)$, then $\tilde K(x) \ge K^\star(x)$, where $\tilde K(x) = 1$ iff $2c\, p(x, y = 1) > p(x, y = 0)$ is the likelihood-ratio classifier of structure itself. So every window that $K^\star$ flags is also flagged by $\tilde K$. The motif-based rule is a valid but less powerful classifier of $y = 1$ versus $y = 0$.

**Calibrated calls.** For each motif window $z$, a statistic $S$ (robust Mahalanobis distance of $F_\theta(z)$ combined with $L_1$ reconstruction error) is compared with its empirical distribution on held-out B-DNA $X^B_{te}$. The lower-tail p-value is

$$p = \frac{\#\{x \in X^B_{te} : S(x) \le S(z)\}}{|X^B_{te}|},$$

with the upper tail $1 - p$, and the Benjamini–Hochberg procedure at level $\alpha$ is applied over all motif windows.

## Expansion

Since $d \ge 0$, $K \ge 0$. Values $K > 1$ only increase the first term, so it suffices to minimize pointwise over $K(x) \in [0, 1]$. There the integrand is

$$\delta K(x)\bigl[p(x \mid y = 0, s = 0) - \omega\, p(x \mid s = 1)\bigr] + \text{const},$$

which is linear in $K(x)$. The minimum is at $K = 1$ when $\omega\, p(x \mid s = 1) > p(x \mid y = 0, s = 0)$ and at $K = 0$ otherwise. Rewriting the conditional densities as joint densities over $p(s = 1)$ and $p(y = 0, s = 0)$ gives the threshold $c$. $K^\star$ involves the motif label $s$, so on its own it does not classify structure. The comparison with $\tilde K$ shows that its calls are a subset of those of the structure-based likelihood-ratio test. Applied to human nanopore data, motif windows of every non-B type showed significantly shifted translocation-time quantiles relative to B-DNA. At FDR level $0.2$ the method made the most calls on most non-B types.

## Sources

- M. Hosseini, A. Palmer, W. Manka, P. G. S. Grady, V. Patchigolla, J. Bi, R. J. O'Neill, Z. Chi, D. Aguiar, "Deep statistical modelling of nanopore sequencing translocation times reveals latent non-B DNA structures", Bioinformatics 39 (2023) i242–i251, Section 3, Section 4.2, Equations (1)–(5), Proposition 1 and Section 4.2.1, <https://doi.org/10.1093/bioinformatics/btad220> (PMC10311326).
