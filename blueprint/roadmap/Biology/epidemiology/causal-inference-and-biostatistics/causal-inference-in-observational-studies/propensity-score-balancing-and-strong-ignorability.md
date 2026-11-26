# The propensity score is a balancing score that preserves strong ignorability

**Setting.** Each unit has covariates $X$ taking values in a space $\mathcal X$, a binary treatment $Z \in \{0, 1\}$ and potential
responses $(r_1, r_0)$. The **propensity score** is $e(x) = \Pr(Z = 1 \mid X = x)$. A function $b(X)$ is a **balancing score** if

$$X \perp Z \mid b(X),$$

i.e. the conditional law of $X$ given $b(X)$ is the same for treated and control units. Treatment assignment is **strongly ignorable
given $X$** if

$$(r_1, r_0) \perp Z \mid X \qquad \text{and} \qquad 0 < e(x) < 1 \ \text{ for all } x .$$

**Theorem.**
1. $e(X)$ is a balancing score, and the finest balancing score $b(X) = X$ is also one.
2. A function $b(X)$ is a balancing score if and only if $b$ is finer than $e$, i.e. $e(X) = f(b(X))$ for some function $f$.
3. If treatment assignment is strongly ignorable given $X$, it is strongly ignorable given any balancing score $b(X)$:
   $(r_1, r_0) \perp Z \mid b(X)$ and $0 < \Pr(Z=1 \mid b(X)) < 1$.
4. Consequently, under strong ignorability given $X$, for any balancing score $b$,

$$E\{r_1 \mid b(X), Z = 1\} - E\{r_0 \mid b(X), Z = 0\} = E\{r_1 - r_0 \mid b(X)\},$$

and averaging over the law of $b(X)$ gives the average treatment effect $E(r_1 - r_0)$.

## Expansion

For (1), $\Pr\{Z = 1 \mid X, e(X)\} = e(X)$ and, by the tower property, $\Pr\{Z = 1 \mid e(X)\} = E\{e(X)\mid e(X)\} = e(X)$, so
$Z$ is independent of $X$ given $e(X)$. For the "only if" in (2), if $b$ is not finer than $e$ there are $x_1, x_2$ with
$b(x_1) = b(x_2)$ but $e(x_1) \ne e(x_2)$, which contradicts the equality of $\Pr(Z = 1 \mid X)$ across $X$ within a level of $b$. For
(3), $\Pr\{Z = 1 \mid r_1, r_0, b(X)\} = E\{\Pr(Z = 1 \mid r_1, r_0, X) \mid r_1, r_0, b(X)\} = E\{e(X) \mid r_1, r_0, b(X)\}$, which
equals $e(X)$ because $e(X)$ is a function of $b(X)$, so $Z$ is independent of $(r_1, r_0)$ given $b(X)$. Item (4) then follows since
within a level of $b(X)$ treated and control units are random samples for each potential response. This justifies matching,
subclassification and covariance adjustment on the scalar $e(X)$ in place of the full covariate vector.

## Sources

- P. R. Rosenbaum and D. B. Rubin, "The Central Role of the Propensity Score in Observational Studies for Causal Effects", Biometrika (1983), <https://doi.org/10.1093/biomet/70.1.41>.
