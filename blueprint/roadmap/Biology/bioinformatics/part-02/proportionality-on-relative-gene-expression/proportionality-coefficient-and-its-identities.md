# Proportionality coefficient and its identities

**Setting.** Let $X_1, \dots, X_d$ be the parts of a random composition (relative expression of $d$ genes in one library), let $s$ be the unobserved total amount of mRNA, and let $A_i = \log(s X_i)$ be the logged absolute amounts. Genes $i$ and $j$ are proportional when $s X_i \approx m\, s X_j$ across conditions for a constant $m$, that is when the log-ratio variance $\operatorname{var}(A_i - A_j)$ is close to $0$. Assume $\operatorname{var}(A_i) > 0$ and $\operatorname{var}(A_j) > 0$ wherever $r$, $\beta$ or $\phi$ appear, and write $r = \operatorname{corr}(A_i, A_j)$ and $\beta = \sqrt{\operatorname{var}(A_j)/\operatorname{var}(A_i)}$ (the absolute value of the standardized major axis slope of $A_j$ against $A_i$).

**Definition.** For random variables with $\operatorname{var}(A_i) + \operatorname{var}(A_j) > 0$, the proportionality coefficient (a special case of Lin's concordance correlation coefficient) is

$$\rho(A_i, A_j) = \frac{2\operatorname{cov}(A_i, A_j)}{\operatorname{var}(A_i) + \operatorname{var}(A_j)} \in [-1, 1],$$

with $\rho = 1$ exactly for $\operatorname{var}(A_i - A_j) = 0$ (proportional pair) and $\rho = -1$ exactly for $\operatorname{var}(A_i + A_j) = 0$ (reciprocal pair). The asymmetric statistic $\phi(A_i, A_j) = \operatorname{var}(A_i - A_j)/\operatorname{var}(A_i) = 1 + \beta^2 - 2\beta r$ is related to it by $\phi = (1 - \rho)(1 + \beta^2)$.

**Proposition 1.** With $\tilde\beta^2 = \operatorname{var}(A_i - A_j)/\operatorname{var}(A_i + A_j)$ (when $\operatorname{var}(A_i + A_j) > 0$),

1. $\displaystyle \rho(A_i, A_j) = 1 - \frac{\operatorname{var}(A_i - A_j)}{\operatorname{var}(A_i) + \operatorname{var}(A_j)}$,
2. $\displaystyle \rho(A_i, A_j) = \frac{2r}{\beta + 1/\beta}$,
3. $\displaystyle \rho(A_i, A_j) = \frac{1 - \tilde\beta^2}{1 + \tilde\beta^2}$, which equals $1 - 2/(1 + 1/\tilde\beta^2)$ when moreover $\operatorname{var}(A_i - A_j) > 0$,
4. $\displaystyle \rho(A_i + A_j, A_i - A_j) = \frac{1 - \beta^2}{1 + \beta^2}$.

## Expansion

Write $v_i = \operatorname{var}(A_i)$, $S = A_i + A_j$ and $D = A_i - A_j$. Identity 1 is $\operatorname{var}(D) = v_i + v_j - 2\operatorname{cov}(A_i, A_j)$. Identity 2 follows from $\operatorname{cov}(A_i, A_j) = r\sqrt{v_i v_j}$ after dividing numerator and denominator by $\sqrt{v_i v_j}$, so $\rho$ is $r$ shrunk by the ratio of the geometric to the arithmetic mean of the two variances. Identity 3 uses $\operatorname{var}(S) + \operatorname{var}(D) = 2(v_i + v_j)$, so $1 - \rho = \operatorname{var}(D)/(v_i + v_j) = 2\operatorname{var}(D)/(\operatorname{var}(S) + \operatorname{var}(D))$: the coefficient compares the within-pair variance $\operatorname{var}(D)$ with the group variance $\operatorname{var}(S)$, the two diagonals of the parallelogram spanned by the centred sample vectors. Identity 4 follows from $\operatorname{cov}(S, D) = v_i - v_j$, which gives the duality between the pair and its sum and difference.

Scaling the log-ratio variance by $v_i + v_j$ is natural because $\operatorname{var}(D) \le 2(v_i + v_j)$, with equality for reciprocal pairs. The individual variances $v_i$ are not observable on relative data; they reappear as log-ratio variances against a reference once the data are log-ratio transformed, which is what makes the choice of reference matter.

## Sources

- I. Erb, C. Notredame, "How should we measure proportionality on relative gene expression data?", Theory in Biosciences 135 (2016) 21–36, Eqs. (1)–(2) and Proposition 1, <https://doi.org/10.1007/s12064-015-0220-8>, PMCID PMC4870310.
