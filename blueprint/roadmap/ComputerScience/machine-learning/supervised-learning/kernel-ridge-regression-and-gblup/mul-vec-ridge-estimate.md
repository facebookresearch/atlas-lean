# RR-BLUP = GBLUP (predictions)

**RR-BLUP = GBLUP** (predictions): let $\iota$ be a finite set of markers, $Z \in \mathbb{R}^{m \times \iota}$ the training genotypes, $y \in \mathbb{R}^m$ and $\lambda > 0$, and let $\hat\beta = (Z^\top Z + \lambda I)^{-1} Z^\top y$ be the ridge marker effects. For any genotypes $Z' \in \mathbb{R}^{\tau \times \iota}$ (training or new individuals), $Z' \hat\beta = Z' Z^\top (Z Z^\top + \lambda I)^{-1} y$.
