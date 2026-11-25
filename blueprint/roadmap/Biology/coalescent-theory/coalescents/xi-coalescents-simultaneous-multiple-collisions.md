# Merger rates of a coalescent with simultaneous multiple collisions

Let $\Delta = \{\zeta = (\zeta_1, \zeta_2, \dots) : \zeta_1 \ge \zeta_2 \ge \dots \ge 0,\ \sum_i \zeta_i \le 1\}$, write $|\zeta| = \sum_i \zeta_i$ and $(\zeta, \zeta) = \sum_i \zeta_i^2$, and let
$\Xi = a\,\delta_0 + \Xi_0$ with $a \ge 0$ and $\Xi_0$ a finite measure on $\Delta$ with $\Xi_0(\{0\}) = 0$. For $b$ blocks, integers $k_1, \dots, k_r \ge 2$ and $s \ge 0$ with
$k_1 + \dots + k_r + s = b$, the **Ξ-merger rate** is

$$\lambda_{b; k_1, \dots, k_r; s} = a\,\mathbf 1\{r = 1, k_1 = 2\} + \int_\Delta \sum_{l=0}^{s} \binom sl (1 - |\zeta|)^{s-l} \sum_{i_1, \dots, i_{r+l}\ \text{distinct}} \zeta_{i_1}^{k_1} \cdots \zeta_{i_r}^{k_r}\, \zeta_{i_{r+1}} \cdots \zeta_{i_{r+l}}\ \frac{\Xi_0(d\zeta)}{(\zeta, \zeta)} ,$$

the rate at which, among $b$ blocks, $r$ given disjoint groups of sizes $k_1, \dots, k_r$ each merge into one block while the remaining $s$ blocks stay
unchanged; the order of $k_1, \dots, k_r$ does not matter. Each rate is finite, at most $a + \Xi_0(\Delta)$: since $k_1 \ge 2$, $\zeta_{i_1}^{k_1} \le \zeta_{i_1}^2$, so the inner sum is at most $(\zeta, \zeta)\, |\zeta|^{r - 1 + l}$, and
$\sum_{l=0}^{s} \binom sl (1 - |\zeta|)^{s-l} |\zeta|^l = 1$, so the integrand is at most $|\zeta|^{r-1} \le 1$. Finiteness of $\Xi_0$ is
needed; $\int (\zeta, \zeta)\, \Xi_0(d\zeta) < \infty$ is not enough, since $\Xi_0 = \sum_m \delta_{(1/m, 0, 0, \dots)}$ satisfies it but has infinite pair rate. The rates are
consistent: adding a block, which stays single, joins one of the $r$ groups, or forms a new pair with one of the $s$ unchanged blocks,

$$\lambda_{b; k; s} = \lambda_{b+1; k; s+1} + \sum_{j=1}^r \lambda_{b+1; k + e_j; s} + s\, \lambda_{b+1; k, 2; s-1} .$$

When $\Xi$ is concentrated on $\{\zeta : \zeta_2 = \zeta_3 = \dots = 0\}$, every rate with $r \ge 2$ vanishes and, with $\Lambda$ the image of $\Xi$ under $\zeta \mapsto \zeta_1$, the rate with $r = 1$
is [Pitman's merger rate](merger-rate.md) $\lambda_{b, k_1}$; the consistency relation then reduces to Pitman's [recursion](merger-rate-consistent.md).

## Depends on

- [Pitman's merger rate](merger-rate.md)

## Related topics

- [Pitman's consistency relation](merger-rate-consistent.md)

## Sources

- M. Birkner, J. Blath, M. Möhle, M. Steinrücken and J. Tams, "A modified lookdown construction for the Xi-Fleming-Viot process with mutation and populations with recurrent bottlenecks", arXiv:0808.0412 (2008), Section 1.3, equation (1.1), quoting J. Schweinsberg, "Coalescents with simultaneous multiple collisions", Electronic Journal of Probability 5 (2000), Theorem 2. The consistency relation is checked numerically for $b \le 5$.
