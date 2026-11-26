# Burden and cost comparison of elimination orderings

**Setting.** Two areas $i = 1, 2$ have transmission potentials (control reproduction numbers) $R_1 > R_2 > 1$, pre-elimination burdens per unit time $B_1 > B_2$, burdens $b_i$ per unit time during intensified control, and require intensified control for durations $T_i$ to interrupt transmission. Strategy $A$ eliminates in area 1 first, then area 2; strategy $B$ the reverse. After elimination an area keeps a surveillance system that prevents re-establishment, while its transmission potential returns to the pre-intervention value; it receives imported infections at rate $V_i$ (its vulnerability) while the other area is still endemic. Each imported case costs $\beta$ and each of its secondary cases costs $\gamma$. In low-transmission settings $V_1 \approx \eta(R_2 - 1)$ and $V_2 \approx \eta(R_1 - 1)$, with $\eta$ the migration intensity, reflecting prevalence $p = 1 - 1/R \approx R - 1$ in the source.

**Proposition.**
1. (Burden) The total burdens are $E_A = (b_1 + B_2)T_1 + b_2T_2$ and $E_B = (b_2 + B_1)T_2 + b_1T_1$, so

$$\Delta E = E_B - E_A = B_1T_2 - B_2T_1 .$$

Hence with equal durations $T_1 = T_2$, strategy $A$ always minimizes burden (and with many areas, burden is minimized by proceeding in order of decreasing burden); if $T_1 > T_2$, strategy $A$ minimizes burden if and only if $B_1/B_2 > T_1/T_2$.
2. (Cost) The additional importation cost of strategy $A$ over $B$ is

$$\Delta C = V_1T_2(\beta + \gamma R_1) - V_2T_1(\beta + \gamma R_2).$$

With equal durations $T$ and low-transmission vulnerabilities, $\Delta C = \eta T(\beta + \gamma)(R_2 - R_1) < 0$, so targeting the higher-transmission area first is also cheaper; with $T_1 > T_2$ and low-transmission vulnerabilities this remains true. With saturated (high-transmission) vulnerabilities $V_1 = V_2$ and equal durations, $\Delta C = VT\gamma(R_1 - R_2) > 0$, so strategy $B$ is cheaper.

## Expansion

Burden accrues in the first area during its control phase, in the second area at the pre-elimination level until its own control starts, and then during the second area's control phase; subtracting the two totals cancels the $b_i$ terms. For cost, the area cleared first is the only one exposed to importation, for the duration of the second area's program, and each import generates on average $R$ secondary cases in the receiving area, which surveillance must find; this gives $\Delta C$. In the low-transmission case the vulnerability of each area is proportional to the other area's excess transmission, $R_j - 1$, so the factors combine to $\eta T[(R_2 - 1)(\beta + \gamma R_1) - (R_1 - 1)(\beta + \gamma R_2)] = \eta T(\beta + \gamma)(R_2 - R_1)$. With saturating relations $B_i, V_i, T_i \propto 1 - e^{-\psi(R_i - 1)}$, the preferred order for cost depends on the actual transmission levels: low overall transmission and a low ratio of secondary-case to imported-case cost favor treating the higher-transmission area first.

## Sources

- N. Chitnis, A. Schapira, C. Schindler, M. A. Penny, T. A. Smith, "Mathematical analysis to prioritise strategies for malaria elimination", Journal of Theoretical Biology (2018), Table 1, Eqs. (1)–(11), Tables 2–3 and Appendices B–I, <https://doi.org/10.1016/j.jtbi.2018.07.007>, PMCID PMC6117457.
