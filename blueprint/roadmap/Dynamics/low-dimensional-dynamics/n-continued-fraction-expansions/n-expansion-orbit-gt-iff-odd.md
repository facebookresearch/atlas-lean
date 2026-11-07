# Orbits with the same digits alternate in order

Let $N$ be a positive integer and let
$0 < \alpha < \alpha'$ be real numbers. Write $T_\alpha$ for the $N$-expansion map and $d_\alpha$
for the $N$-expansion digit with parameter $\alpha$, and let $m$ be a natural number. If the
orbits $\alpha_j = T_\alpha^j(\alpha)$ and $\alpha'_j = T_{\alpha'}^j(\alpha')$ satisfy
$d_\alpha(\alpha_j) = d_{\alpha'}(\alpha'_j)$ for all $j \in \{0, \dots, m\}$, then
$\alpha'_m < \alpha_m$ if and only if $m$ is odd. Likewise, if the orbits
$\beta_j = T_\alpha^j(\alpha + 1)$ and $\beta'_j = T_{\alpha'}^j(\alpha' + 1)$ satisfy
$d_\alpha(\beta_j) = d_{\alpha'}(\beta'_j)$ for all $j \in \{0, \dots, m\}$, then
$\beta'_m < \beta_m$ if and only if $m$ is odd.

The paper assumes $\alpha$ and $\alpha'$ in Phase I (so in particular $\alpha' \le \sqrt N - 1$);
for $N > 0$ neither assumption is needed (the orbits stay in $[\alpha, \alpha + 1]$ and
$[\alpha', \alpha' + 1]$, where $x \mapsto N/x$ is strictly decreasing), so both are replaced by
$N > 0$. For $N = 0$ the claim fails ($\alpha = 1/5$, $\alpha' = 3/10$, $m = 1$).

## Sources

- Jaap de Jonge, *Intervals of N-Expansions with Many Gaps*, INTEGERS 26 (2026), Article A75, Lemma 2.
