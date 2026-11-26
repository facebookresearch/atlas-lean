# Battery port balance

For all real $\eta_c$, $\eta_d$, $P_c$, $P_d$ (real division, with $x/0 = 0$, so the identity also holds for $\eta_d = 0$),

$$P_c - P_d = \left(\eta_c P_c - \frac{P_d}{\eta_d}\right) + (1 - \eta_c)\, P_c + \left(\frac{1}{\eta_d} - 1\right) P_d:$$

the terminal power absorbed by the battery splits into the storage power $\eta_c P_c - P_d/\eta_d$ and the remainder $(1 - \eta_c) P_c + (1/\eta_d - 1) P_d$. As an algebraic identity this holds for all real inputs. The remainder is the nonnegative dissipated power only under the model assumptions: nonnegative powers $P_c, P_d \ge 0$ and efficiencies $\eta_c, \eta_d \in (0, 1]$. Outside them it can be negative: $P_c = 0$, $P_d = 1$, $\eta_c = 1$, $\eta_d = 0$ give $-1$.
