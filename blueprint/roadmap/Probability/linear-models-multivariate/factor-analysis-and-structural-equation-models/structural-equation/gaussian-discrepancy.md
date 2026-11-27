# Gaussian covariance-fit discrepancy

For real $p \times p$ matrices $S$ (sample) and $C$ (model), the Gaussian discrepancy is $F(S, C) = \log\det C + \operatorname{tr}(SC^{-1}) - \log\det S - p$. It is meaningful for positive definite $S$ and $C$; elsewhere it uses $\log 0 = 0$, $\log x = \log|x|$ for $x < 0$, and $C^{-1} = 0$ for singular $C$.

## Sources

- P. L. Bartlett, lecture notes for STAT 241A, University of California, Berkeley (2007), Lemma 2.
