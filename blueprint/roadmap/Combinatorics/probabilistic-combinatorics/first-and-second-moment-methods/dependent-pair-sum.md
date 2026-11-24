# Correlation sum over dependent pairs

For events $A_i$ indexed by a finite set and a graph $G$ on the indices (a dependency graph),

$$\Delta = \sum_{(i, j) \,:\, i \sim_G j} \Pr[A_i \cap A_j],$$

the sum running over ordered adjacent pairs. With this convention $\operatorname{Var} X \le \mu + \Delta$ ([variance bound](variance-sum-indicator-le.md)); Zhao's notes write $\Delta$ over unordered pairs $i < j$, for which the same bound needs $2\Delta$. The ordered convention agrees with the $\Delta$ of [Janson's inequalities](../janson-s-inequalities/README.md).

## Sources

- Yufei Zhao (lecturer) and Andrew Lin (notes), *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, Section 4.2 (definition of $\Delta$ before Corollary 4.13).
