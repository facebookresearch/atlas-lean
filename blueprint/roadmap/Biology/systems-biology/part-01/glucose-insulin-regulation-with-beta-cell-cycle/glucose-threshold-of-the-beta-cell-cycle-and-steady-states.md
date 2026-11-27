# Glucose threshold of the β-cell cycle and steady states of the glucose–insulin system

**Model.** β-cells in phases $G_1$ (functioning mass), $S$ and $G_2/M$ obey

$$\dot G_1 = 2p_3\,G_2M - \big(p_1(1 + p_5G) + p_4\big)G_1, \qquad \dot S = p_1(1+p_5G)\,G_1 - p_2S, \qquad \dot{G_2M} = p_2S - p_3\,G_2M,$$

where $p_1(1+p_5G)$ is the glucose-dependent $G_1 \to S$ transition rate, $p_4$ the apoptosis rate and the factor $2$ counts the two daughters of a division. Blood glucose $G$ and insulin $I$ follow

$$\dot G = p_6 - (p_7 + p_8I)\,G, \qquad \dot I = \frac{p_9}{bv}\,X_1 - p_{10}I,$$

with net hepatic production $p_6$, glucose effectiveness $p_7$, insulin sensitivity $p_8$, blood volume $bv$, secretion of the releasable insulin pool $X_1$ at rate $p_9$ and insulin clearance $p_{10}$; $X_1$, a reserve pool $X_2$ and a provision factor $P$ (relaxing to a Hill function $P_\infty(G) = G^h/(P_0^h + G^h)$) complete an eight-dimensional system with all parameters positive.

**Proposition.**
1. *(Positivity.)* Solutions with positive initial data stay positive, since each right-hand side is positive when its own variable is set to zero and the others are positive.
2. *(Glucose threshold.)* The cell-cycle subsystem has a non-trivial equilibrium only if $p_4 = p_1(1+p_5G)$, i.e. at

$$\hat G = \frac{p_4 - p_1}{p_1p_5};$$

for glucose $G_t < \hat G$ apoptosis exceeds entry into $S$ and the functioning β-cell mass declines, while for $G_t > \hat G$ it grows.
3. *(Steady states.)* The full system has exactly two equilibria with non-negative cell numbers: the trivial state $F_1^* = (0,0,0,\,p_6/p_7,\,0,0,0,\,P_\infty(p_6/p_7))$ without β-cells, which is unstable, and a non-trivial state $F_2^*$ with

$$G^* = \hat G, \qquad I^* = \frac{p_6 - p_7G^*}{p_8G^*}, \qquad X_1^* = \frac{bv\,p_{10}I^*}{p_9}, \qquad S^* = \frac{p_4}{p_2}G_1^*, \qquad G_2M^* = \frac{p_4}{p_3}G_1^*,$$

which is stable for the physiological parameter set (requiring $p_7\hat G < p_6$ so that $I^* > 0$).

## Expansion

At an equilibrium, $G_2M = p_2S/p_3 = p_1(1+p_5G)G_1/p_3$, and substituting into $\dot G_1 = 0$ gives $\big(p_1(1+p_5G) - p_4\big)G_1 = 0$: either there are no cells or the glucose level equals $\hat G$. The β-cell mass thus acts as integral control on glucose: any persistent deviation of $G$ from $\hat G$ changes the mass, which changes insulin secretion until glucose returns to the threshold, while the insulin and storage equations then determine $I^*$, $X_1^*$, $G_1^*$ and $P^*$. Without β-cells, glucose settles at $p_6/p_7$, above the threshold for physiological parameters, so the empty state is unstable.

## Sources

- M. Gallenberger, W. zu Castell, B. A. Hense, C. Kuttler, "Dynamics of glucose and insulin concentration connected to the β-cell cycle: model development and analysis", Theoretical Biology and Medical Modelling 9 (2012) 46, Mathematical model, Eqs (1)–(3) and (9), Corollary 1 (Eq (10)), steady states Eqs (11)–(16) and the stability analysis, <https://doi.org/10.1186/1742-4682-9-46>, PMCID PMC3585463.
