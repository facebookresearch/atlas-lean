# Nash equilibrium of a two-fleet fishery with quadratic harvesting

**Setting.** A fish stock $N$ grows logistically with intrinsic rate $r$ and carrying capacity $K$ and is harvested with the nonlinear (quadratic) harvest function $H = qEN^2$, where $E$ is fishing effort and $q$ the catchability:

$$\frac{dN}{dt} = rN\Big(1 - \frac{N}{K}\Big) - qEN^2 = rN\Big(1 - \frac{N}{K_0}\Big), \qquad K_0 = \frac{rK}{r + qEK}.$$

Two fleets choose efforts $E_1, E_2 \ge 0$ simultaneously (a static game with complete information), share the equilibrium harvest in proportion to effort, sell at price $P$ and pay cost $C$ per unit effort:

$$U_j(E_1,E_2) = \frac{qP\,r^2K^2\,E_j}{\big(r + q(E_1+E_2)K\big)^2} - C\,E_j .$$

**Proposition.**
1. The positive equilibrium $N = K_0$ is globally asymptotically stable for $N(0) > 0$, and the equilibrium (sustainable) harvest at total effort $E$ is $H(E) = qE\big(rK/(r+qEK)\big)^2$.
2. (Best responses.) Let $A = r^2P/(qC)$ and $\beta = r/(qK) + E_2$. If $E_2 < r\big(\sqrt{P/(qC)} - 1/(qK)\big)$, fleet 1's payoff has a unique maximiser $E_1^\circ > 0$, the unique real root of

$$E_1^3 + 3\beta E_1^2 + (3\beta^2 + A)E_1 = A\beta - \beta^3,$$

given by Cardano's formula $E_1^\circ = \big(A(\beta + \sqrt{\beta^2 + A/27})\big)^{1/3} + \big(A(\beta - \sqrt{\beta^2 + A/27})\big)^{1/3} - \beta$; otherwise the best response is $E_1 = 0$. The same holds for fleet 2 by symmetry, and Nash equilibria are the intersections of the two best-response curves.
3. (Inefficiency.) For $r = P = 1$, $q = C = 1/\sqrt{27}$, $K = \sqrt{27}$, the unique Nash equilibrium is $(E_1^\ast,E_2^\ast) = (1,1)$, with total harvest $H(2) = 2\sqrt{27}/9 \approx 1.15$. The same total harvest is obtained with total effort $1/2$, so the noncooperative equilibrium spends four times the effort needed; an agreement on reduced effort makes both fleets better off.

## Expansion

Quadratic harvesting rescales the carrying capacity rather than shifting the growth rate, so the stock never collapses under any finite effort, and the sustainable yield $H(E)$ is hump-shaped in effort: it rises like $qE K^2$ for small effort and decays like $r^2/(q E)$ for large effort. The first-order condition $\partial U_1/\partial E_1 = 0$ becomes $(E_1 + \beta)^3 = A(\beta - E_1)$ after writing $r + q(E_1+E_2)K = qK(E_1 + \beta)$, whose left side is increasing and right side decreasing in $E_1$, so the interior best response is unique. In the numerical example $qK = 1$ and $A = 27$, so the symmetric equilibrium solves $(2E+1)^3 = 27$, i.e. $E = 1$; the equal-harvest efforts solve $2E^2 - 5E + 2 = 0$, i.e. $E \in \{1/2, 2\}$. The waste is the familiar tragedy of the commons: each fleet ignores the reduction of the stock, and hence of the other fleet's catch, caused by its own effort.

## Sources

- Elahe Sorouri, Madjid Eshaghi Gordji, Reza Memarbashi, "An analysis of a fishing model with nonlinear harvesting function", International Journal of Nonlinear Analysis and Applications 11 (2020), 73–80, <https://doi.org/10.22075/ijnaa.2020.4217>. Published version of arXiv:1905.05823, cited next; locators there refer to the arXiv version.
- Elahe Sorouri, Madjid Eshaghi Gordji, Reza Memarbashi, "An Analysis of a Fishing Model with Nonlinear Harvesting Function", arXiv:1905.05823 (2019), Section 2 (model, equilibria, best-response functions, Equations 2.1–2.6, Nash equilibrium and the numerical example), <https://doi.org/10.48550/arXiv.1905.05823>.
