# A section maximizer solves the fixed-shape score equation

For a design $X$, offset $o$ and counts $y$, let $\ell(\beta, \theta)$ be the joint negative binomial log-likelihood, $\ell_0(\theta) = \ell(\beta_0, \theta)$ its restriction to the null $\beta = \beta_0$, and $\ell_{\mathrm{prof}}(\theta) = \sup_\beta\ell(\beta, \theta)$ the profile log-likelihood of the shape. For $\theta > 0$, if $\hat\beta$ maximizes $b \mapsto \ell(b, \theta)$, then the fixed-shape score $X^\top s$ vanishes at $\hat\beta$.
