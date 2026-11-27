# Best-off cell payoff in two-type versus three-type hawk–dove tumours

**Game.** A tumour has $n$ cells meeting in random pairs to contest a resource $v$; fighting costs $c > v$. A cell that is aggressive with probability $\alpha$ against an opponent aggressive with probability $\beta$ has expected payoff

$$u(\alpha, \beta) = \frac v2(1 - \beta) + \frac c2\Big(\frac vc - \beta\Big)\alpha,$$

so the homogeneous population has the unique evolutionarily stable strategy (ESS) $\alpha = v/c$. In a heterogeneous tumour, cells recognize the type $I$ of their opponent but not their own, so a strategy is a vector $(\alpha_I)_I$ of aggression levels toward each type, and a cell maximizes the type-averaged payoff $U = \sum_I x_I U_I$, where $x_I$ are type proportions and $U_I$ averages $u$ over opponents met with probabilities $(nx_J - \mathbf 1[J = I])/(n-1)$. Whenever all cells use the same strategy, $U_I > U_J \iff \alpha_I < \alpha_J$: the best-off type is the one receiving the least aggression. Let

$$\bar x_A = \Big(1 - \frac vc\Big)\Big(1 - \frac1n\Big), \qquad \bar x_E = \frac vc\Big(1 - \frac1n\Big).$$

For example, with $n = 10$ and $v/c = 1/2$, $\bar x_A = \bar x_E = 0.45$; these are exactly the values at which the formulas below for $\alpha_B$ reach $1$ and $0$.

**Proposition.**
1. (Two types, low heterogeneity) For types $A, B$ with $x_A < \bar x_A$, the ESS in which $A$ is best off is $\big(\alpha_A, \alpha_B\big) = \big(0,\ \tfrac{n-1}{n - nx_A - 1}\tfrac vc\big)$; the best-off payoff $U_A^{**}(x_A)$ increases and is convex in $x_A$ on this range, and the aggression on $B$ saturates at $1$ when $x_A$ reaches $\bar x_A$.
2. (Three types, high heterogeneity) For types $A, B, E$ there is an ESS with $U_A > U_B > U_E$ if and only if $x_A < \bar x_A$ and $x_E < \bar x_E$, namely

$$(\alpha_A, \alpha_B, \alpha_E) = \Big(0,\ \frac{(n-1)v/c - nx_E}{n - nx_A - nx_E - 1},\ 1\Big);$$

the best-off payoff $U_A^{***}(x_A, x_E)$ increases in $x_A$ and decreases in $x_E$. For $x_A > \bar x_A$ there is instead an ESS with $\alpha_B = \alpha_E$, reproducing the two-type outcome.
3. (Heterogeneity penalizes the best-off clone) If $y_A < \bar x_A$ and $x_E < \bar x_E$, then $U_A^{**}(y_A) > U_A^{***}(y_A, x_E)$: at equal proportion of the best-off type, its cells earn more in the two-type tumour than in the three-type tumour.

## Depends on

- [Evolutionarily stable state of a matrix game](../../../population-dynamics/stability-of-evolutionarily-stable-states/is-ess.md)

## Expansion

Since $u$ is linear in the cell's own strategy, $U = f(\beta) + \sum_I f_I(\beta)\alpha_I$ with $f_I(\beta) \propto \frac{nx_I}{n-1}\big(\frac vc(1 - \frac1n) - \sum_J x_J\beta_J + \frac{\beta_I}{n}\big)$, so at a symmetric equilibrium each $\alpha_I$ is $0$, $1$, or interior with $f_I = 0$. Making $A$ untouched ($\alpha_A = 0$), $E$ fully attacked ($\alpha_E = 1$) and $B$ indifferent ($f_B = 0$) gives the formula for $\alpha_B$ in part 2, and the requirement $0 < \alpha_B < 1$ gives the two thresholds; stability against invasion follows from the sign pattern of the $f_I$. In both games the best-off cells receive no aggression, but with a third, fully attacked type present, less aggression is directed at $B$ cells, so $A$ cells more often meet hawkish opponents and win the resource less often; comparing the closed forms gives part 3. Biologically, more diverse tumours restrain their most aggressive clone, consistent with better outcomes observed for high-heterogeneity renal tumours in the motivating case series.

## Sources

- A. Laruelle, A. Rocha, C. Manini, J. I. López, E. Inarra, "Effects of heterogeneity on cancer: a game theory perspective", Bulletin of Mathematical Biology 85 (2023) 72, Eqs. (1)–(7) and Propositions 1–3 (proofs in Appendices B–F), <https://doi.org/10.1007/s11538-023-01178-9>, PMCID PMC10279587.
