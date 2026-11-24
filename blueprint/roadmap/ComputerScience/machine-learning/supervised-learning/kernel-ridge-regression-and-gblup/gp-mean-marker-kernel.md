# GP posterior mean = GBLUP

Let $\iota$ be a finite set of markers, $Z' \in \mathbb{R}^{\tau \times \iota}$ and $Z \in \mathbb{R}^{m \times \iota}$ genotype matrices, and $s, \sigma^2 > 0$. For the [marker kernel](marker-kernel.md) with variance $s$, the predictive-mean matrix of Gaussian-process regression is $K(Z', Z) (K(Z, Z) + \sigma^2 I)^{-1} = Z' Z^\top (Z Z^\top + (\sigma^2/s) I)^{-1}$.
