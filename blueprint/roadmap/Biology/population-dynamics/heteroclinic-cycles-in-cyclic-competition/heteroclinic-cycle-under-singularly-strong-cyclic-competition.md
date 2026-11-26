# Heteroclinic cycle under singularly strong cyclic competition

**Model.** Three competitors with rock–paper–scissors (cyclic) dominance obey
$$v_1' = v_1(1 - v_1 - k_{12}v_2 - k_{13}v_3), \quad v_2' = v_2\big(1 - \tfrac1\varepsilon v_1 - v_2 - k_{23}v_3\big), \quad v_3' = v_3(1 - k_{31}v_1 - k_{32}v_2 - v_3),$$
where species 1 exerts a singularly strong pressure $1/\varepsilon$ on species 2, $0 < \varepsilon \ll 1$, and
$$0 < k_{12},k_{23},k_{31} < 1, \quad k_{13},k_{32} > 1, \quad k_{13}(1-k_{31}) > 1, \quad k_{32}(1-k_{23}) > 1, \quad k_{13}+k_{31} > 2, \quad k_{32}+k_{23} > 2,$$
with $\varepsilon < \min\{k_{12},1-k_{12},1/(2-k_{12})\}$. Rescaling $u_1 = v_1/\varepsilon$, $u_2 = v_2$, $u_3 = v_3$ gives the regular-looking system $u_1' = u_1(1 - \varepsilon u_1 - k_{12}u_2 - k_{13}u_3)$, $u_2' = u_2(1 - u_1 - u_2 - k_{23}u_3)$, $u_3' = u_3(1 - \varepsilon k_{31}u_1 - k_{32}u_2 - u_3)$, whose single-species equilibria $E_1 = (1/\varepsilon,0,0)$, $E_2 = (0,1,0)$, $E_3 = (0,0,1)$ are saddles on the boundary.

**Theorem (one dominance pattern).** Start on the section $u_1 = 1$ with $u_2(0) \in (\delta_1^-,\delta_1^+)$ small and $u_3(0) \in (1-\delta_2,1)$. For $\varepsilon$ small and $\delta_1^+$, $\delta_2$ below explicit thresholds, the return time $T = \inf\{t>0 : u_1(t) = 1,\ u_1'(t) < 0\}$ is finite: the solution passes near $E_3$, then $E_2$, then $E_1$ and back. With constants $0<\lambda^+<\lambda^-\lesssim 1$ and $0<\kappa\lesssim1$ depending only on $(k_{ij})$,
$$\ln\delta_1^- - \lambda^-\ln\varepsilon \lesssim \frac{\ln u_2(T)}{1 + 1/\varepsilon} \lesssim \ln\delta_1^+ - \lambda^+\ln\varepsilon, \qquad \ln\big(1 - u_3(T)\big) \lesssim \ln\varepsilon,$$
$$-\ln\delta_1^+ + \kappa\ln\varepsilon \lesssim T \lesssim -\ln\delta_1^- - \ln\varepsilon, \qquad \tfrac1\varepsilon \lesssim \max_{[0,T]}u_1 < \tfrac1\varepsilon,$$
and at some intermediate time $u_2 \ge k_0 = \frac12\big(1 - k_{23} + 1/k_{32}\big) > 0$: the weakest species becomes extremely small at the start and end of each pattern yet recovers to an order-one density during it.

**Theorem (heteroclinic cycle and $\omega$-limit).** For each fixed small $\varepsilon$ there are three heteroclinic orbits $\Gamma_{32}$, $\Gamma_{21}$, $\Gamma_{13}$ on the boundary, connecting $E_3 \to E_2 \to E_1 \to E_3$. The pattern repeats indefinitely, the solution shadows each orbit over the successive pattern intervals, and
$$\operatorname{dist}\big(u(t),\ \Gamma_{32}\cup\Gamma_{21}\cup\Gamma_{13}\big) \to 0 \qquad (t\to\infty).$$
Solutions with positive data are bounded: $\limsup u_1 \le 1/\varepsilon$, $\limsup u_2 \le 1$, $\limsup u_3 \le 1$.

## Expansion

Near each saddle the flow is approximately linear, so the passage time is governed by logarithms of entry distances, and the exit distance is a power of the entry distance; composing the three passages gives the return map. The large factor $1/\varepsilon$ makes the contraction at $E_1$ exponentially strong in $1/\varepsilon$, which explains the scaling $\ln u_2(T)/(1+1/\varepsilon)$. The structural conditions make the product of the expansion–contraction ratios favorable, so successive patterns drive the orbit ever closer to the boundary cycle.

## Sources

- Arnaud Ducrot, Quentin Griette and Quang-Vinh Tran, "Heteroclinic cycles and long-time behavior in a singularly perturbed three-species Lotka--Volterra system", arXiv:2610.06908 (2026), Theorem 2.2 (one complete pattern), Proposition 2.3, Theorem 2.4 (heteroclinic cycle), Theorems 2.5 and 2.6 (shadowing and $\omega$-limit set), Proposition 3.1, <https://doi.org/10.48550/arXiv.2610.06908>.
