# Secant criterion for cyclic feedback: further results

Arcak and Sontag (2006) extend the [secant criterion for diagonal stability](secant-criterion-diagonal-stability-of-cyclic-negative-feedback.md) from the linear cyclic matrix to nonlinear cyclic interconnections. (1) For a negative-feedback cycle of blocks $H_1, \dots, H_n$ with inputs $u_1 = -y_n$, $u_i = y_{i-1}$, each block having a $C^1$ storage function $V_i$ with $\dot V_i \le -y_i^2 + \gamma_iu_iy_i$ (output strict passivity with gain $\gamma_i > 0$), the secant condition $\gamma_1\cdots\gamma_n < \sec(\pi/n)^n$ yields weights $d_i > 0$ such that $V = \sum_id_iV_i$ satisfies $\dot V \le -\varepsilon|y|^2$ for some $\varepsilon > 0$ (their Corollary 1); the same holds when some blocks are static nonlinearities with $0 \le -y_i^2 + \gamma_iu_iy_i$. (2) Suppose instead that $H_1, \dots, H_{n-1}$ satisfy the passivity inequality above with $C^1$ storage functions and gains $\gamma_i > 0$, that $H_n$ is the linear block with transfer function $\gamma_na_n/(s + a_n)$, $a_n > 0$, $\gamma_n > 0$, and that the feedback is a time-invariant nonlinearity $\psi$ in the sector of their condition (22) with $\psi(y) = 0$ only for $y = 0$. Then $\kappa\gamma_1\cdots\gamma_n < \sec(\pi/n)^n$ (their condition (27)), with $\kappa$ the sector bound $0 \le y\psi(y) \le \kappa y^2$ of their condition (22), gives a Lyapunov function $V = \sum_{i<n}d_iV_i + d_n\int_0^{y_n}\psi(\tau)\,d\tau$ with $\dot V \le -\varepsilon|(y_1, \dots, y_{n-1}, \psi(y_n))|^2$ (their Corollary 2, which extends the relaxed condition of Tyson and Othmer). (3) For the biochemical cycle $\dot x_1 = -f_1(x_1) + g_n(x_n)$, $\dot x_i = -f_i(x_i) + g_{i-1}(x_{i-1})$ ($i \ge 2$) on the nonnegative orthant, under their sign, unique-equilibrium and sector assumptions (A1)–(A3) with constants $\gamma_i$, the secant condition implies that the equilibrium is asymptotically stable, and globally on the nonnegative orthant under the additional growth condition (52) (their Corollary 4).

## Depends on

- [Secant criterion for diagonal stability of cyclic negative feedback](secant-criterion-diagonal-stability-of-cyclic-negative-feedback.md)

## Expansion

1. Output strict passivity and storage functions for each block, and the static-block variant.
2. The weighted Lyapunov function from the diagonal stability of the linear comparison matrix, as in Corollary 1; asymptotic stability then needs a detectability argument (the source leaves the choice of stability conclusion open).
3. The biochemical cycle (1), the assumptions (A1)–(A3), the change of variables to the passive form, and Corollary 4 with its growth condition.
4. Corollary 2, by combining the linear block and the sector nonlinearity into one output strictly passive block with gain $\gamma_n\kappa$, so that condition (27) is the secant condition for the gains $\gamma_1, \dots, \gamma_{n-1}, \gamma_n\kappa$.

## Sources

- M. Arcak and E. D. Sontag, Diagonal stability of a class of cyclic systems and its connection with the secant criterion, Automatica 42 (2006), 1531–1537, Corollaries 1, 2 and 4, conditions (22) and (27). <https://doi.org/10.1016/j.automatica.2006.04.009>
