# Penalty and horizon Gamma-convergence for capacity-constrained epidemic control

**Problem.** For the SEIR model with suppression $h(t) \in [0, h_{\max}]$ ($h_{\max} < \beta$) and delayed vaccination $u(t) \in [0, u_{\max}]$ ($u = 0$ before $t_{\mathrm{delay}}$), let $\mathcal{U}_{\mathrm{ad}}$ be the admissible control pairs, equipped with the weak-$*$ topology of $L^\infty$. With discount rate $\delta > 0$ and cost coefficients $c_H, c_{NH}, c_V \ge 0$, the running cost is

$$L_0 = c_H\, i\, h + c_{NH}\, i + c_V\, u\, s .$$

Given a capacity $I_{\max} \in (0,1)$, the **hard-constrained** problem minimizes $J_{\mathrm{strict}}(u,h) = \int_0^\infty L_0\, e^{-\delta t} dt$ over controls whose trajectory satisfies $i(t) \le I_{\max}$ for all $t$ (and $J_{\mathrm{strict}} = +\infty$ otherwise). The **penalized** problem minimizes

$$J_\kappa(u,h) = \int_0^\infty \bigl( L_0 + \kappa \max\{0, i - I_{\max}\}^2 \bigr) e^{-\delta t}\, dt,$$

and $J_{\kappa, T}$ denotes the same integral truncated at a finite horizon $T$.

**Theorem.**

1. If controls converge weakly-$*$ in $\mathcal{U}_{\mathrm{ad}}$, a subsequence of the trajectories converges uniformly on every $[0, T]$.
2. For every $\kappa > 0$ the penalized problem has an optimal control.
3. If the hard-constrained problem has a feasible control, then $J_{\kappa_n}$ $\Gamma$-converges to $J_{\mathrm{strict}}$ as $\kappa_n \to \infty$, and every sequence of penalized minimizers has a subsequence converging to a minimizer of the hard-constrained problem.
4. For fixed $\kappa, \delta > 0$, $J_{\kappa, T_n}$ $\Gamma$-converges to $J_\kappa$ as $T_n \to \infty$, and minimizers over large finite horizons have subsequences converging to an infinite-horizon minimizer.

Thus finite-horizon penalized numerical solutions approximate the optimal policy that strictly respects healthcare capacity over an infinite horizon.

## Depends on

- [Asymptotics and final-size bound for the SEIR model with suppression and vaccination](final-size-bound-for-seir-with-suppression-and-vaccination.md)

## Expansion

The admissible set is weak-$*$ compact, and because the controls enter the dynamics affinely the states depend continuously on them, giving equi-coercivity and lower semicontinuity of the costs (the cost is affine in the controls given the state). For the penalty limit, a weak-$*$ limit whose trajectory exceeds $I_{\max}$ somewhere exceeds it by a margin on an interval, so the penalty diverges (liminf inequality), while feasible controls are their own recovery sequence because the penalty vanishes. For the horizon limit, the discount factor makes the tail $\int_T^\infty$ uniformly small. The fundamental theorem of $\Gamma$-convergence then transfers minimizers.

## Sources

- Behrooz Moosavi Ramezanzadeh, "Optimal Control of an Epidemic with Intervention Design", arXiv (2025). Lemma 3.1, Theorem 3.2, Theorem 3.3, Theorem 3.4. <https://doi.org/10.48550/arXiv.2503.22928>
