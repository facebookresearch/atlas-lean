# GP posterior mean = RR-BLUP

Let $\iota$ be a finite set of markers, $Z' \in \mathbb{R}^{\tau \times \iota}$ and $Z \in \mathbb{R}^{m \times \iota}$ genotype matrices, $y \in \mathbb{R}^m$ and $s, \sigma^2 > 0$. With the [marker kernel](marker-kernel.md) $k$ of variance $s$, the Gaussian-process predictive mean at the genotypes $Z'$ is $K(Z', Z) (K(Z, Z) + \sigma^2 I)^{-1} y = Z' \hat\beta$, where $\hat\beta = (Z^\top Z + \lambda I)^{-1} Z^\top y$ are the ridge marker effects with $\lambda = \sigma^2 / s$.
