# Partner strategies in linked multichannel donation games

Two players interact repeatedly in $m$ independent donation games played in parallel. In game $k$, cooperation means paying a cost $c_k > 0$ to give the co-player a benefit $b_k > c_k$, so the one-round payoffs are $R_k = b_k - c_k$, $S_k = -c_k$, $T_k = b_k$, $P_k = 0$; a player's payoff is the sum of the limiting average payoffs over the $m$ games, and errors occur with a small probability $\varepsilon$.

A **reactive** strategy conditions only on the co-player's actions in the previous round. In the *unlinked* case the strategy set is $\mathcal R_U = \{(p^k_{a_k}) : p^k_{a_k} \in [0,1]\}$, where $p^k_{a_k}$ is the cooperation probability in game $k$ given the co-player's last action $a_k \in \{C,D\}$ in *that* game. In the *linked* case it is $\mathcal R_L = \{(p^k_{\mathbf a}) : \mathbf a \in \{C,D\}^m\}$, conditioning on the co-player's whole last action profile; $\mathcal R_U \subsetneq \mathcal R_L$.

Call a strategy a **partner** if it is a Nash equilibrium against every strategy, of any complexity, and is self-cooperative in every game. With the indicator $e^k_{\mathbf a} = 1$ exactly when the $k$-th entry of $\mathbf a$ is $C$:

- a self-cooperative $\mathbf p \in \mathcal R_L$ is a partner **iff** $\displaystyle \sum_{k=1}^{m} b_k\bigl(1 - p^k_{\mathbf a}\bigr) \;\ge\; \sum_{k=1}^{m} c_k \bigl(1 - e^k_{\mathbf a}\bigr)$ for every $\mathbf a \in \{C,D\}^m$;
- a self-cooperative $\mathbf p \in \mathcal R_U$ is a partner **iff** $p^k_D \le 1 - c_k/b_k$ for every game $k$.

For $m = 2$ the linked condition reads $p^1_{CC} = p^2_{CC} = 1$ together with the three weighted averages

$$\frac{b_1 p^1_{DC} + b_2 p^2_{DC}}{b_1 + b_2} \le 1 - \frac{c_1}{b_1+b_2}, \quad \frac{b_1 p^1_{CD} + b_2 p^2_{CD}}{b_1+b_2} \le 1 - \frac{c_2}{b_1+b_2}, \quad \frac{b_1 p^1_{DD} + b_2 p^2_{DD}}{b_1+b_2} \le 1 - \frac{c_1+c_2}{b_1+b_2} .$$

The unlinked conditions bind game by game, the linked conditions only on a benefit-weighted average, so a linked player may be more forgiving in one game by being less forgiving in another, and the set of cooperation-sustaining strategies is strictly larger.

## Remarks

The analogous characterizations hold for the other two equilibrium classes: a self-defective $\mathbf p \in \mathcal R_L$ is a *defector* iff $\sum_k b_k p^k_{\mathbf a} \le \sum_k c_k e^k_{\mathbf a}$ for all $\mathbf a$, and a strategy self-cooperative in game $k$ but self-defective elsewhere is a *game-$k$ semi-partner* iff $b_k(1 - p^k_{\mathbf a}) - c_k(1 - e^k_{\mathbf a}) \ge \sum_{l \ne k} b_l p^l_{\mathbf a} - \sum_{l\ne k} c_l e^l_{\mathbf a}$ for all $\mathbf a$. With $m = 1$ the linked and unlinked conditions coincide and both reduce to $p_D \le 1 - c/b$, the maximum forgiveness of Generous Tit-for-Tat, so the classical repeated-game characterization is the special case of one channel. Under random strategy exploration the measure of partner strategies is larger in the linked case, especially when the games differ in benefit, while semi-partners and defectors become rarer; this is the mechanism behind the simulated increase in cooperation under linkage, in which evolving strategies reduce cooperation in *both* games after a defection in either — Linked Tit-for-Tat.

## Sources

- K. Donahue, O. P. Hauser, M. A. Nowak, C. Hilbe, "Evolving cooperation in multichannel games", *Nature Communications* 11 (2020), 3885, <https://doi.org/10.1038/s41467-020-17730-3> (PMC7403149). Results, "Characterization of partners, semi-partners, and defectors", Equations (4)–(5); Methods, "Analytical results for reactive strategies", Equations (6)–(7) and Propositions 1–4.
