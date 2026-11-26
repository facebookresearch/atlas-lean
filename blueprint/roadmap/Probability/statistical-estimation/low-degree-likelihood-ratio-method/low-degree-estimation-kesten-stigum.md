# Low-degree Bayesian estimation reaches the Kesten–Stigum threshold

There is an efficient meta-algorithm for Bayesian estimation that computes the best low-degree polynomial approximation of the posterior moments of the hidden parameters (computed from self-avoiding-walk statistics) and recovers the parameters by robust tensor decomposition. In the symmetric sparse stochastic block model with $k$ communities (within-community edge probability $a/n$, across-community $b/n$) it achieves weak recovery whenever $(a-b)^2 > k\,(a + (k-1)b)$, the Kesten–Stigum threshold, and for the mixed-membership stochastic block model with constant average degree it recovers up to the conjectured computational threshold. Below the Kesten–Stigum threshold, the low-degree analysis gives evidence that the task requires time $\exp(n^{\Omega(1)})$ when $k$ is large enough that recovery is information-theoretically possible.

## Proof sketch

Self-avoiding walk counts between two vertices are unbiased low-degree estimators of their community correlation; their variance is controlled exactly when the branching factor times the squared second eigenvalue of the community matrix exceeds one, which is the Kesten–Stigum condition. Below the threshold, the low-degree advantage of the corresponding testing problem stays bounded at degree $n^{\Omega(1)}$, which by the low-degree conjecture predicts subexponential hardness.

## Depends on

- [Low-degree likelihood ratio and low-degree advantage](low-degree-likelihood-ratio.md)

## Proof depends on

- [Low-degree conjecture](low-degree-conjecture.md)

## Sources

- S. B. Hopkins, D. Steurer, "Efficient Bayesian Estimation from Few Samples: Community Detection and Related Problems", FOCS (2017), arXiv:1710.00264.
