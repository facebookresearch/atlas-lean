# Bounds on total target in the TMDD model

**Setting.** Consider the [basic TMDD model](basic-tmdd-model-and-its-conservation-laws.md) with baseline target $R_0 = k_{in}/k_{out}$ and total target $R_{tot} = R + RL$, started from baseline $R_{tot}(0) = R_0$ (with $RL(0) = 0$), under any bolus or constant-rate dosing.

**Lemma.** For all $t \ge 0$,

$$R_{tot}(t) \;\le\; \max\Big\{\frac{k_{in}}{k_{out}},\ \frac{k_{in}}{k_{e(RL)}}\Big\} = \max\Big\{1,\ \frac{k_{out}}{k_{e(RL)}}\Big\}\, R_0.$$

The bound does not depend on the dose, the dosing regime or the binding constants.

## Depends on

- [Basic TMDD model and its conservation laws](basic-tmdd-model-and-its-conservation-laws.md)

## Expansion

From the conservation law, $\dot R_{tot} = k_{in} - k_{out} R - k_{e(RL)} RL$ with $R, RL \ge 0$. If $k_{e(RL)} \ge k_{out}$, then $k_{out} R_{tot} \le k_{out} R + k_{e(RL)} RL \le k_{e(RL)} R_{tot}$, so $k_{in} - k_{e(RL)} R_{tot} \le \dot R_{tot} \le k_{in} - k_{out} R_{tot}$. Comparison with the linear equation whose equilibrium is $k_{in}/k_{out} = R_0$, started from $R_0$, gives $R_{tot}(t) \le R_0$; if $k_{e(RL)} < k_{out}$ the inequalities swap and comparison with the equation whose equilibrium is $k_{in}/k_{e(RL)}$ gives $R_{tot}(t) \le (k_{out}/k_{e(RL)})\,R_0$. Together these are the Lemma.

*Remark (lower bounds, not stated in the source).* The same comparison, applied to the other side of each differential inequality, also gives

$$
\begin{cases}
\dfrac{k_{out}}{k_{e(RL)}}\, R_0 \;\le\; R_{tot}(t), & \text{if } k_{e(RL)} \ge k_{out},\\[2ex]
R_0 \;\le\; R_{tot}(t), & \text{if } k_{e(RL)} < k_{out},
\end{cases}
$$

so when $k_{e(RL)} = k_{out}$ the total target stays at $R_0$ for all time, the classical special case in which the complex is eliminated at the same rate as free target.

## Sources

- L. A. Peletier and J. Gabrielsson, "Dynamics of target-mediated drug disposition: characteristic profiles and parameter identification", *Journal of Pharmacokinetics and Pharmacodynamics* (2012), Appendix 3 ("Bounds of the receptor concentration"), Lemma 1 and its proof (cases I and II). <https://doi.org/10.1007/s10928-012-9260-6> (PMC3446204)
