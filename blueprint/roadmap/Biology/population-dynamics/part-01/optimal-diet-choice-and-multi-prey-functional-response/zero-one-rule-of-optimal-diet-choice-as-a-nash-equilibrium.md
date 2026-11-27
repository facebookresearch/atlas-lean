# Zero-one rule of optimal diet choice as a Nash equilibrium

**Model.** A predator repeatedly searches microhabitats. Each search takes time $\tau_s > 0$ and finds a prey of type $1$ with probability $p_1$, of type $2$ with probability $p_2$, and nothing otherwise ($p_1, p_2 > 0$, $p_1 + p_2 \le 1$, probabilities constant in time). On encountering type $i$ the predator attacks with probability $q_i\in[0,1]$; an attack costs handling time $h_i > 0$ and yields energy $e_i > 0$. By renewal theory the long-run energy intake rate is mean energy per cycle over mean cycle length:

$$R(q_1, q_2) = \frac{p_1q_1e_1 + p_2q_2e_2}{\tau_s + p_1q_1h_1 + p_2q_2h_2},$$

and the functional response to prey $i$ is $f_i = p_iq_i/(\tau_s + p_1q_1h_1 + p_2q_2h_2)$. With one prey type and $q = 1$ this is the Holling type II response.

**Zero-one rule.** Rank prey by profitability and suppose $e_1/h_1 > e_2/h_2$. Then every maximiser of $R$ has $q_1 = 1$, and the less profitable prey is included as follows:

$$q_2 = \begin{cases} 1 & \text{if } \dfrac{e_2}{h_2} > \dfrac{p_1e_1}{\tau_s + p_1h_1},\\[2mm] 0 & \text{if } \dfrac{e_2}{h_2} < \dfrac{p_1e_1}{\tau_s + p_1h_1},\\[2mm] \text{any value in } [0,1] & \text{if equality holds.}\end{cases}$$

Equivalently, prey $2$ is taken iff $p_1 < p_1^\ast = \dfrac{e_2\tau_s}{e_1h_2 - e_2h_1}$: the decision depends only on the encounter rate with the better prey, not on the abundance of prey $2$ itself.

**Game-theoretic reading.** Treat each decision node of the foraging decision tree as a virtual player whose payoff is the common rate $R$. A strategy pair $(q_1^\ast, q_2^\ast)$ is a Nash equilibrium if $R(q_1, q_2^\ast)\le R(q_1^\ast, q_2^\ast)$ and $R(q_1^\ast, q_2)\le R(q_1^\ast, q_2^\ast)$ for all $q_1, q_2$. Every optimal foraging strategy is a Nash equilibrium. In this two-prey model attacking prey $1$ strictly dominates, and the Nash equilibria are exactly the zero-one rule above; at the critical encounter rate the equilibria form a whole segment (a Nash equilibrium component). In larger decision trees (for example with costly prey recognition) suboptimal Nash equilibria can exist.

## Expansion

$R$ is a ratio of affine functions of $q_2$ with positive denominator, so $\partial R/\partial q_2$ has the sign of $e_2(\tau_s + p_1q_1h_1) - h_2p_1q_1e_1$, independent of $q_2$; this forces a corner solution except at the threshold. The same sign argument applied to $q_1$, using $e_1/h_1 > e_2/h_2$ and $R < e_1/h_1$, shows attacking the most profitable prey always raises the rate. The threshold is the classical statement that a prey type enters the diet iff its profitability exceeds the intake rate achievable without it.

## Sources

- R. Cressman, V. Křivan, J. S. Brown, J. Garay, *Game-theoretic methods for functional response and optimal foraging behavior*, PLoS ONE 9 (2014), e88773, sections "Decision trees and functional response for two prey types" and "Decision trees and extensive form games" (Eqs. 1–4). <https://doi.org/10.1371/journal.pone.0088773> (PMCID: PMC3938838)
