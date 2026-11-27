# Expected exposure effects under misspecified exposure mappings

Let units $i = 1, \dots, n$ have potential outcomes $y_i(z)$ for assignments $z \in \mathcal{Z}$, a random assignment $Z$ from a known design, and an exposure mapping giving each unit an exposure $D_i = d_i(Z)$ in a finite set $\Delta$. The mapping is correctly specified if $y_i(z)$ depends on $z$ only through $d_i(z)$; it need not be. Define the expected potential outcome $\bar y_i(d) = \mathbb{E}\{y_i(Z) \mid D_i = d\}$ and, for exposures $a, b \in \Delta$, the expected exposure effect

$$\tau(a, b) = \frac{1}{n} \sum_{i=1}^{n} \bigl\{\bar y_i(a) - \bar y_i(b)\bigr\}.$$

With $\pi_i(d) = \Pr(D_i = d) > 0$ and $D_{id} = 1[D_i = d]$, the Horvitz–Thompson estimator

$$\hat\tau(a, b) = \frac{1}{n} \sum_{i=1}^{n} \frac{D_{ia} Y_i}{\pi_i(a)} - \frac{1}{n} \sum_{i=1}^{n} \frac{D_{ib} Y_i}{\pi_i(b)}$$

is unbiased for $\tau(a, b)$ however severely the exposures are misspecified. When the mapping is correctly specified, $\tau(a, b)$ equals the usual exposure effect of Aronow and Samii.

## Expansion

$\mathbb{E}\{D_{ia} Y_i\} = \pi_i(a)\, \mathbb{E}\{y_i(Z) \mid D_i = a\} = \pi_i(a) \bar y_i(a)$, so each term of $\hat\tau$ has the right mean. The definition marginalizes over all assignments that map to the same exposure, so it depends on the design; the exposure is used to define the effect, not to assume away interference beyond it. The specification error $\varepsilon_i = y_i(Z) - \bar y_i(D_i)$ measures what the mapping misses.

## Sources

- F. Sävje, *Causal inference with misspecified exposure mappings: separating definitions and assumptions*, Biometrika (2023). <https://doi.org/10.1093/biomet/asad019> Definitions 1 and 2, and Section 5.1 (unbiasedness via Aronow and Samii 2017, Proposition 8.1; supplement Lemma S4).
