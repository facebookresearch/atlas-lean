# Majority-type sufficient condition for identifying multivariable Mendelian randomization

In the population version of the [multivariable Mendelian randomization model](multivariable-mr-ivw-and-egger.md), let $\tilde\beta_{Yj}$ and $\tilde\beta_{Xj} = (\tilde\beta_{Xj1}, \dots, \tilde\beta_{XjK})$ be the population regression coefficients of the outcome and the risk factors on variant $j$, so that

$$\tilde\beta_{Yj} = \alpha_j + \tilde\beta_{Xj}^\top\theta, \qquad j = 1, \dots, p.$$

Let $V = \{j : \alpha_j = 0\}$ be the set of valid instruments and assume the association vectors are in general position: any $K$ of the vectors $\tilde\beta_{X1}, \dots, \tilde\beta_{Xp}$ are linearly independent.

**Statement.** If

$$|V| > \frac{p + K - 1}{2},$$

then $\theta$ is identified as the unique $q \in \mathbb{R}^K$ maximizing $\#\{j : \tilde\beta_{Yj} = \tilde\beta_{Xj}^\top q\}$, and then each $\alpha_j = \tilde\beta_{Yj} - \tilde\beta_{Xj}^\top\theta$ is identified. For $K = 1$ this is the sufficient condition "more than half of the variants are valid" of the plurality-valid rule. Under general position the condition implies the [multivariable plurality assumption](multivariable-mr-plurality-identifiability.md), which is necessary and sufficient for identification.

## Depends on

- [Multivariable inverse-variance weighted and MR-Egger estimators](multivariable-mr-ivw-and-egger.md)
- [Identifiability of multivariable Mendelian randomization under a plurality rule](multivariable-mr-plurality-identifiability.md)

## Expansion

Every $j \in V$ satisfies the relation with $q = \theta$. If $q \ne \theta$ and $W_q = \{j : \tilde\beta_{Yj} = \tilde\beta_{Xj}^\top q\}$, then each $j \in V \cap W_q$ satisfies $\tilde\beta_{Xj}^\top(\theta - q) = 0$; by general position at most $K - 1$ such vectors are orthogonal to the nonzero vector $\theta - q$. Hence $|W_q| \le (p - |V|) + (K - 1) < |V|$ under the stated condition, so $\theta$ is the strict plurality solution. The paper states the condition in this form after recalling the univariable result of Kang and coauthors.

## Sources

- A. J. Grant and S. Burgess, "Pleiotropy robust methods for multivariable Mendelian randomization", Statistics in Medicine 40 (2021), section 2.3, "Model identification", Equation (3), <https://doi.org/10.1002/sim.9156> (PMC7612169).
