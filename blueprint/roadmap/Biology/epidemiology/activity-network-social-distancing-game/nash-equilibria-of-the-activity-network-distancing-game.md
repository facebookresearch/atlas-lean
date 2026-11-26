# Nash equilibria of the activity-network distancing game

**Game.** Let $V = \{1,\dots,n\}$ be a set of activities with contact values $\alpha_i > 0$ and symmetric connectivity matrix $A$ ($A_{ii} = 1$; $A_{ij} = 1$ if individuals in activities $i$ and $j$ meet, else $0$). Define the weighted connectivity matrix
$$A^{\alpha}_{ij} = A_{ij}\,\frac{\alpha_i + \alpha_j}{2}, \qquad A^{\alpha} = \tfrac12 (AW + WA), \quad W = \mathrm{diag}(\alpha).$$
A strategy is a point $x$ of the simplex $S = \{x \in \mathbb{R}^n_{\ge 0} : \sum_i x_i = 1\}$, with $x_i$ the frequency of participation in activity $i$. An individual with strategy $x$ in a population with average strategy $y$ makes $x^{\top}A^{\alpha}y$ social contacts, and seeks to minimise it. A strategy $x^* \in S$ is a (symmetric) Nash equilibrium if $x^{\top}A^{\alpha}x^* \ge x^{*\top}A^{\alpha}x^*$ for all $x \in S$.

**Theorem 1 (equilibrium conditions).** With $p_i(x) = \sum_j A^{\alpha}_{ij}x_j$, $x^*$ is a Nash equilibrium if and only if there is a scalar $\lambda^*$ with
$$p_i(x^*) = \lambda^* \text{ whenever } x_i^* > 0, \qquad p_i(x^*) \ge \lambda^* \text{ whenever } x_i^* = 0.$$
Then $\lambda^* = x^{*\top}A^{\alpha}x^*$ is the equilibrium number of contacts.

**Theorem 2 (independent regular groups).** Let $V^* = V_1^* \cup \dots \cup V_m^*$ be a maximal independent set of activity groups (no connections between different groups), where every activity of $V_i^*$ is connected to exactly $r_i$ other activities of $V_i^*$ and all have contact value $\alpha_i$; let $m_i = |V_i^*|$. Put $x_j^* = 0$ for $j \notin V^*$ and choose $x_j^* > 0$ on $V^*$ with
$$\sum_{j \in V_i^*} x_j^* = \frac{\lambda^* m_i}{\alpha_i (r_i + 1)}, \qquad \frac{1}{\lambda^*} = \sum_{i=1}^m \frac{m_i}{\alpha_i(r_i+1)}.$$
If moreover $p_j(x^*) \ge \lambda^*$ for all $j \notin V^*$, then $x^*$ is a Nash equilibrium (an optimal distancing strategy). For a maximal independent set of single activities ($r_i = 0$, $m_i = 1$) this gives $x_i^* = \lambda^*/\alpha_i$ with $1/\lambda^* = \sum_{i \in V^*} 1/\alpha_i$.

## Expansion

Theorem 1 is the Karush–Kuhn–Tucker condition for minimising the linear function $x \mapsto x^{\top}A^{\alpha}x^*$ over the simplex: a mixed strategy is a best response exactly when all activities it uses give the same, minimal, contact payoff. In Theorem 2, an activity $j \in V_i^*$ meets only its own group, so $p_j(x^*) = \alpha_i\,(x_j^* + \sum_{k \sim j} x_k^*)$; summing the equalities $p_j(x^*) = \lambda^*$ over the $m_i$ activities of a regular group counts each group member $r_i + 1$ times, giving $\alpha_i(r_i+1)\sum_{j \in V_i^*}x_j^* = \lambda^* m_i$, and normalising over all groups fixes $\lambda^*$. Equilibrium contacts are therefore a harmonic-type mean of the group contact values: concentrating participation in many disconnected, low-contact activities lowers $\lambda^*$.

## Sources

- Z. Wu, "Social distancing is a social dilemma game played by every individual against his/her population", PLoS ONE 16 (2021) e0255543, Methods, Theorems 1–2, <https://doi.org/10.1371/journal.pone.0255543>, PMCID PMC8328347.
