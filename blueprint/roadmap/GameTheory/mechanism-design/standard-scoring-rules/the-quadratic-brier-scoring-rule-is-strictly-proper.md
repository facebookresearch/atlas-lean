# The quadratic (Brier) scoring rule is strictly proper

On a finite outcome set $\Omega$, the quadratic scoring rule $S(p, \omega) = 2 p(\omega) - \sum_{\omega'} p(\omega')^2$ and the Brier score $-\sum_{\omega'} (p(\omega') - \mathbf 1[\omega' = \omega])^2$ are strictly proper on the whole probability simplex, with quadratic scores in $[-1, 1]$; any positive affine transformation $a + bS$ with $b > 0$ is strictly proper with range $[a - b, a + b]$.

## Proof sketch

The expected score under belief $q$ of report $p$ is $\|q\|^2 - \|p - q\|^2$, uniquely maximized at $p = q$.

## Depends on

- [Characterization of proper scoring rules](../characterization-of-proper-scoring-rules.md)
- [Scoring rules and properness for finite outcomes](../remaining-clauses-of-scoring-rules-and-properness.md)

## Sources

- Eric Friedman, Paul Resnick and Rahul Sami, "Manipulation-Resistant Reputation Systems", Algorithmic Game Theory, Cambridge University Press, 2007.
- Glenn W. Brier, "Verification of Forecasts Expressed in Terms of Probability", Monthly Weather Review, 1950.
- Tilmann Gneiting and Adrian E. Raftery, "Strictly Proper Scoring Rules, Prediction, and Estimation", Journal of the American Statistical Association, 2007.
