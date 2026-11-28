# Stability of laminar patterns via the quotient spectral radius

**Setting.** Take the cell-type-weighted lateral-inhibition network on a stratified bilayer from [Existence of laminar patterns under cell-type-weighted lateral inhibition](existence-of-laminar-patterns-under-cell-type-weighted-lateral-inhibition.md): equitable layer partitions $P_L, P_B$ with bipartite reduced graphs, $n_1$ same-type and $n_2$ other-type neighbours with weights $w_1, w_2$, $R_\tau = n_1/n_2$. Let a laminar steady state have representative basal and luminal inputs, and let $q_B, q_L > 0$ be the $\mathcal L_2$-gains of the representative cells, which for monotone SISO cells equal the steady-state (dc) gains $q = |T'(u_s)|$ at the respective inputs.

**Theorem (stability of laminar patterns).** If

$$\frac{n_1 w_1 (q_B + q_L) + \sqrt{\bigl(n_1 w_1 (q_B - q_L)\bigr)^2 + \bigl(2 n_2 w_2 \sqrt{q_B q_L}\bigr)^2}}{2 (n_1 w_1 + n_2 w_2)} < 1,$$

then the heterogeneous steady states of the basal and luminal layers are locally asymptotically stable. Writing $a = n_1 w_1/N_w$ and $b = n_2 w_2/N_w$, the condition is equivalent to

$$q_B q_L (b^2 - a^2) + a (q_B + q_L) < 1 \quad \text{together with} \quad a (q_B + q_L) < 2.$$

**Corollary.** Let $|T'(u^*)| > 1$. If $q_B + q_L \le 2 + \frac{2(|T'(u^*)| + 1)}{|T'(u^*)| - 1}$, then the existence bound $w_1 < \frac{|T'(u^*)| - 1}{|T'(u^*)| + 1} \cdot \frac{w_2}{R_\tau}$ of the companion page implies the side condition $w_1 < \frac{2}{q_B + q_L - 2} \cdot \frac{w_2}{R_\tau}$ (for $q_B + q_L > 2$), under which the stability condition becomes explicit quadratic bounds on $w_1$. The source's Corollary 3.1 prints instead that the side condition holds automatically once $|T'(u^*)| \ge 3$; that is false: for $a = 0.1$, $b = 0.9$ and a decreasing $T$ with $T(1) = 1$, $T'(1) = -3$, $T(0.38) = 2$, $T'(0.38) = -100$, $T(1.82) = 0.2$, $T'(1.82) = -0.01$, the state $(y_B, y_L) = (2, 0.2)$ is laminar with $a/b \approx 0.11$ below the existence bound $1/2$ but above the side bound $2/98.01$.

**Relation to the small-gain theorem.** With $q_L < q_B$ and $b > a$, the condition is implied by $q_B\bigl((b^2 - a^2) q_B + 2a\bigr) < 1$, which holds whenever $q_B < 1$. Conversely, since $a + b = 1$, the condition implies the closed-loop small-gain condition $q_B q_L < 1$ (if $p = q_B q_L \ge 1$, its left side is at least $p(b - a) + 2a\sqrt p \ge 1$), so it is stricter than that condition, and the converse fails ($q_B = 2$, $q_L = 0.4$, $a = 0.4$ give $q_Bq_L = 0.8$ but left side $1.12$). The two conditions coincide exactly when $n_1 = 0$ (no same-type neighbours, e.g. checkerboard patterns), where the condition reduces to $q_B q_L < 1$. The source's discussion after its (3.16) says the condition relaxes the small-gain condition; the computation just given shows the implication runs the other way.

## Expansion

The Rufino Ferreira–Arcak stability criterion says a partition pattern is locally asymptotically stable when $\rho\bigl(\frac{1}{N_w} \overline{\mathbf W}\, \overline{\mathbf Q}\bigr) < 1$, with $\overline{\mathbf Q} = \mathrm{diag}(q_B, q_L)$. For the bilayer,

$$\frac{1}{N_w} \overline{\mathbf W}\, \overline{\mathbf Q} = \begin{pmatrix} a q_B & b q_L \\ b q_B & a q_L \end{pmatrix}, \qquad \rho = \frac{a (q_B + q_L)}{2} + \frac{\sqrt{a^2 (q_B - q_L)^2 + 4 b^2 q_B q_L}}{2},$$

which is the displayed left-hand side. Squaring $\sqrt{\cdot} < 2 - a(q_B + q_L)$ gives the polynomial form; substituting $a, b$ in terms of $w_1, w_2$ turns it into a quadratic inequality in $w_1$ whose sign of leading coefficient, $q_B + q_L - q_B q_L - 1$, decides which root bounds $w_1$. The corollary compares this side condition with the existence bound using $q_L < |T'(u^*)| < q_B$.

## Depends on

- [Existence of laminar patterns under cell-type-weighted lateral inhibition](existence-of-laminar-patterns-under-cell-type-weighted-lateral-inhibition.md)

## Sources

- J. W. Moore, T. C. Dale, T. E. Woolley, "Algebraic framework for determining laminar pattern bifurcations by lateral-inhibition in 2D and 3D bilayer geometries", arXiv:2104.12142 (2021), section "Theoretical results" (stability theorem for bilayer laminar patterns, its corollary, and the comparison with the small-gain theorem). <https://doi.org/10.48550/arXiv.2104.12142>
- Published version: J. W. Moore, T. C. Dale, T. E. Woolley, "Polarity-driven laminar pattern formation by lateral-inhibition in 2D and 3D bilayer geometries", IMA Journal of Applied Mathematics (2022), <https://doi.org/10.1093/imamat/hxac011>.
