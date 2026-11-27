# Time-optimal dosing with drug-induced resistance

**Model.** Sensitive ($x_1$) and resistant ($x_2$) tumour fractions share a carrying capacity normalized to $1$. A dose $u(t) \in [0, M]$ (Lebesgue measurable) kills sensitive cells at per-capita rate $d\,u$ and converts them to resistance at rate $\alpha u$, in addition to spontaneous conversion at rate $\epsilon$; resistant cells grow at relative rate $0 \le p_r < 1$ and are unaffected by the drug:

$$\dot x_1 = (1 - x_1 - x_2)\,x_1 - (\epsilon + \alpha u)\,x_1 - d\,u\,x_1, \qquad \dot x_2 = p_r(1 - x_1 - x_2)\,x_2 + (\epsilon + \alpha u)\,x_1,$$

i.e. $\dot x = f(x) + u\,g(x)$ with $g(x) = \big(-(\alpha + d)x_1,\ \alpha x_1\big)^\top$. The simplex $\{x_1, x_2 \ge 0,\ x_1 + x_2 \le 1\}$ is forward invariant and, if $\epsilon > 0$, every solution tends to the fully resistant state $(0, 1)$ whatever the treatment. For a critical volume $V_c \in (0, 1 - \epsilon)$, the failure time is $t_c(u) = \max\{ T : x_1(t) + x_2(t) \le V_c \text{ on } [0, T]\}$, and the problem is to maximize $t_c$ over admissible doses.

**Theorem.**
1. *(Boundary control.)* On the critical line $N = \{x_1 + x_2 = V_c\}$ the dose that holds the tumour volume constant is the feedback

$$u_p(x) = \frac{(1 - V_c)(x_1 + p_r x_2)}{d\,x_1},$$

admissible while $u_p(x) \le M$.
2. *(Interior arcs.)* Before the trajectory first reaches $N$, an optimal trajectory satisfies the unconstrained Pontryagin maximum principle; singular arcs exist only for $\alpha > 0$, on a line segment where the switching function and its derivative vanish, but they are never locally optimal.
3. *(Synthesis.)* For every $\alpha \ge 0$ the optimal dose is a concatenation of bang–bang arcs and the boundary control, with structure $(YX)^n\, u_p\, Y$ read left to right, where $X$ denotes no treatment ($u = 0$) and $Y$ maximal dose ($u = M$): alternating maximal-dose and treatment-free phases, then holding the tumour at $V_c$, then a final maximal-dose arc.

## Expansion

Summing the two equations gives $\frac{d}{dt}(x_1 + x_2) = (1 - V)(x_1 + p_r x_2) - d\,u\,x_1$ with $V = x_1 + x_2$, so setting it to zero on $N$ yields $u_p$; the conversion terms cancel because they move cells between compartments. A dynamic-programming argument shows that the portion of an optimal path before it touches $N$ is itself time-optimal between its endpoints without the path constraint, so the standard maximum principle applies there. Because the control enters linearly, the Hamiltonian is minimized at $u \in \{0, M\}$ unless the switching function $\langle\lambda, g(x)\rangle$ vanishes on an interval; along such an arc its derivative $\langle\lambda, [f, g]\rangle$ must also vanish, which confines singular arcs to a line where $f$, $g$ and the Lie bracket $[f,g]$ are linearly dependent. Comparing times along competing paths by integrating the clock form over the enclosed region (Green's theorem) shows that singular arcs are not optimal and that leaving $N$ and returning is slower than staying on it, which gives the $(YX)^n u_p Y$ structure. Treatment-free phases let sensitive cells outcompete slower-growing resistant cells, delaying failure when the drug itself induces resistance.

## Sources

- J. M. Greene, C. Sanchez-Tapia and E. D. Sontag, "Mathematical details on a cancer resistance model", Frontiers in Bioengineering and Biotechnology 8 (2020), 501, Sections 2–5 (Eqs. (1)–(18), Theorems 1, 15, 17), <https://doi.org/10.3389/fbioe.2020.00501>, PMCID: PMC7325889.
