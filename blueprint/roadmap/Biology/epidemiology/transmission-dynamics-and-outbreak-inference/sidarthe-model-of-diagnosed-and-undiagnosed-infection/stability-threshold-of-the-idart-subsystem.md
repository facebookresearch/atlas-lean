# Stability threshold of the infected subsystem

For the SIDARTHE system write $x = [I\ D\ A\ R\ T]^\top$ and set $r_1 = \varepsilon + \zeta + \lambda$, $r_2 = \eta + \rho$, $r_3 = \theta + \mu + \kappa$, $r_4 = \nu + \xi$, $r_5 = \sigma + \tau$. The infected subsystem is the positive linear system

$$\dot x = Fx + bu, \qquad F = \begin{bmatrix} -r_1 & 0 & 0 & 0 & 0\\ \varepsilon & -r_2 & 0 & 0 & 0\\ \zeta & 0 & -r_3 & 0 & 0\\ 0 & \eta & \theta & -r_4 & 0\\ 0 & 0 & \mu & \nu & -r_5\end{bmatrix}, \quad b = e_1, \quad y_S = c^\top x, \quad c^\top = [\alpha\ \beta\ \gamma\ \delta\ 0],$$

closed by the feedback $u(t) = S(t)\, y_S(t)$. Freezing the gain at a constant $\bar S \ge 0$, the subsystem is asymptotically stable if and only if

$$\bar S < \bar S^{*} = \frac{r_1 r_2 r_3 r_4}{\alpha r_2 r_3 r_4 + \beta \varepsilon r_3 r_4 + \gamma \zeta r_2 r_4 + \delta\big(\eta \varepsilon r_3 + \zeta \theta r_2\big)} .$$

Moreover, for positive initial conditions the limit $\bar S = \lim_{t\to\infty} S(t)$ exists and satisfies $\bar S \le \bar S^{*}$.

## Depends on

- [SIDARTHE model of diagnosed and undiagnosed infection](sidarthe-system.md)

## Proof sketch

With the gain frozen, the eigenvalues of the linearization are the roots of $p(s) = D(s) - \bar S N(s)$, where $G(s) = N(s)/D(s)$ is the transfer function from $u$ to $y_S$ and $D(s) = \prod_{i=1}^{5}(s + r_i)$. Because the system is positive, the $H_\infty$ norm of $G$ is attained at $s = 0$, so a root-locus (small-gain) argument gives the Hurwitz condition $\bar S\, G(0) < 1$, that is $\bar S < 1/G(0) = \bar S^{*}$. The bound on the limit follows by contradiction: $S$ is non-increasing and bounded below, so it converges; if its limit made the frozen system unstable, the Metzler matrix $F + \bar S\, b c^\top$ would have a positive dominant eigenvalue, the infected states could not vanish, and $\dot S$ would stay bounded away from zero, contradicting convergence of $S$.

## Sources

- Giordano G, Blanchini F, Bruno R, et al. Modelling the COVID-19 epidemic and implementation of population-wide interventions in Italy. *Nature Medicine* 26:855-860 (2020), Methods, equations (9)-(17), Propositions 1 and 2. DOI <https://doi.org/10.1038/s41591-020-0883-7>. PMCID PMC7175834.
