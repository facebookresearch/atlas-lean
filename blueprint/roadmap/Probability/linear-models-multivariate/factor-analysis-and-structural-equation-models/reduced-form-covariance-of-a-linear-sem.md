# Reduced form and covariance of a linear structural equation model

Let $y = By + \Gamma x + \zeta$ with real matrices of matching sizes, $I - B$ invertible, $x$ and $\zeta$ centered and square-integrable with $\operatorname{Cov}(x, \zeta) = 0$, $\Phi = \operatorname{Cov}(x)$ and $\Psi = \operatorname{Cov}(\zeta)$. Then $y = (I - B)^{-1}(\Gamma x + \zeta)$ and $\operatorname{Cov}(y) = (I - B)^{-1}(\Gamma\Phi\Gamma^{\mathsf T} + \Psi)(I - B)^{-\mathsf T}$, because $\operatorname{Cov}(\Gamma x + \zeta) = \Gamma\Phi\Gamma^{\mathsf T} + \Psi$ and $\operatorname{Cov}(My) = M\operatorname{Cov}(y)M^{\mathsf T}$. The identity is algebraic and carries no causal interpretation by itself.

## Sources

- K. Vehkalahti, *The matrices of SEM: a few words (and formulas)* (course notes, Structural equation models), University of Helsinki, 2013, Section 'The covariance matrix Σ', equation (5), <https://wiki.helsinki.fi/xwiki/bin/download/SocStats/Structural%20equation%20models%2C%20fall%202014/WebHome/Matrices-of-SEM.pdf?rev=1.2>
