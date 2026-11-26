# Ridge marker effects are back-solved from GBLUP

For a finite set $\iota$ of markers, a genotype matrix $Z \in \mathbb{R}^{m \times \iota}$, phenotypes $y \in \mathbb{R}^m$ and $\lambda > 0$, the ridge marker effects are back-solved from GBLUP: $(Z^\top Z + \lambda I)^{-1} Z^\top y = Z^\top (Z Z^\top + \lambda I)^{-1} y$.
