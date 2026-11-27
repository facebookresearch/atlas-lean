# The Bulmer effect: selection reduces additive variance

Let parents have phenotype $Z = A + E$ with additive value $A$, $\operatorname{Cov}(A, E) = 0$, $V = \operatorname{Var}(A)$, $V_P = \operatorname{Var}(Z)$ and
heritability $h^2 = V/V_P$. Suppose $\mathbb E[A \mid Z]$ is linear in $Z$ and $\operatorname{Var}(A \mid Z)$ is constant, as when $(A, Z)$ is jointly Gaussian, and
let selection keep the parents in an event determined by $Z$ that reduces $\operatorname{Var}(Z)$ by the fraction $\kappa \in [0, 1]$. Then

$$\operatorname{Var}(A \mid \text{selected}) = V(1 - \kappa h^2),$$

because $\operatorname{Var}(A \mid Z) = V(1 - h^2)$ and the regression slope is $h^2$, so the selected variance is $V(1 - h^2) + h^4 V_P (1 - \kappa)$. Under
the [infinitesimal model](infinitesimal-model-definition.md) with non-inbred parents mated at random among the selected, the offspring additive variance is

$$V' = \tfrac12 V (1 - \kappa h^2) + \tfrac12 V_0 .$$

If each generation again satisfies the two regression hypotheses, with fixed environmental variance $V_E$ and $h_t^2 = V_t / (V_t + V_E)$,
the map $V \mapsto \frac12 V(1 - \kappa V/(V + V_E)) + \frac12 V_0$ has derivative in $[(1 - \kappa)/2, \frac12]$, so $V_t$ converges geometrically to its
unique fixed point, strictly below $V_0$ when $\kappa > 0$ and $V_0 > 0$ (for $V_0 = 0$ the fixed point is $0$); with $\kappa = 0$, $V_t = V_0 + 2^{-t}(V_{\mathrm{init}} - V_0)$. Without homoscedasticity the
one-generation identity can fail: if $Z = \pm 1$ with probability $\frac12$ each, $A = -\frac12$ when $Z = -1$, and, when $Z = 1$, $A$ takes the values
$-\frac12, \frac12, \frac32$ with probabilities $\frac14, \frac12, \frac14$, then $\mathbb E[A \mid Z] = Z/2$ is linear, $\operatorname{Cov}(A, Z - A) = 0$, $V = \frac12$ and
$h^2 = \frac12$, but keeping $Z = 1$ ($\kappa = 1$) leaves $\operatorname{Var}(A \mid Z = 1) = \frac12$, not $V(1 - \kappa h^2) = \frac14$.

## Depends on

- [The infinitesimal model of inheritance](infinitesimal-model-definition.md)

## Related topics

- [Breeder's equation](../breeder-s-equation/response-eq.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section IX.9, p. 447 (truncation selection generates linkage disequilibrium that decreases the variance of the trait; Bulmer (1971) gave an approximation correcting for it). The identity and recursion are derived above.
