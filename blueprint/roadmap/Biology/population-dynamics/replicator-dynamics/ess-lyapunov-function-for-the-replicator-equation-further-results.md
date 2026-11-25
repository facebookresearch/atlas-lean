# Lyapunov characterization of evolutionarily stable states: further results

Three clauses accompany the [Lyapunov characterization of evolutionarily stable states](ess-lyapunov-function-for-the-replicator-equation.md). (1) For an interior evolutionarily stable state $p$ of the replicator equation $\dot x_i = x_i((Ax)_i - x\cdot Ax)$, every trajectory starting in the interior of the simplex converges to $p$ (the faces of the simplex are invariant, so trajectories starting there do not): $p\cdot Ax > x\cdot Ax$ holds for all $x \ne p$ in the simplex, and $V(x) = \prod_ix_i^{p_i}$ increases strictly along every interior orbit other than $p$ (Hofbauer and Sigmund 2003, Theorem 7 and the remark after it; Hofbauer 2011, Theorem 2.1). (2) Regular evolutionarily stable strategies are asymptotically stable for the replicator dynamics, and more generally for any smooth payoff-monotonic dynamics satisfying a mild regularity condition, because the linearization of such a dynamics at a rest point is proportional to that of the replicator dynamics (Cressman 1997, as restated by Hofbauer and Sigmund 2003, Sec. 3.2). (3) The converse fails in general: not every asymptotically stable rest point is evolutionarily stable (Hofbauer and Sigmund 2003). A candidate example is the interior rest point $p = (\frac14, \dots, \frac14)$ of the four-member hypercycle with all rates equal ($a_{i,i-1} = 1$, other entries $0$): it is not evolutionarily stable, because $z\cdot Az = 0$ for the tangent vector $z = (1, 0, -1, 0)$; its linearization on the simplex has eigenvalues $-\frac14$ and $\pm\frac{i}{4}$, so linearization does not decide its stability; this page does not claim that it is asymptotically stable, and that nonlinear statement is item 4 of the Expansion.

## Depends on

- [Lyapunov characterization of evolutionarily stable states for the replicator equation](ess-lyapunov-function-for-the-replicator-equation.md)

## Expansion

1. The global inequality for an interior ESS and the Lyapunov function on the whole interior.
2. Regular ESSs and the linearization of the replicator equation at them.
3. The hypercycle replicator equation, its interior rest point, the failure of the ESS condition, and the linearization with a purely imaginary pair.
4. A nonlinear stability proof for the four-member hypercycle (for example by a Lyapunov function adapted to the cyclic structure), to be taken from a source that proves it.

## Sources

- J. Hofbauer and K. Sigmund, Evolutionary game dynamics, Bull. Amer. Math. Soc. (N.S.) 40 (2003), 479–519. <https://doi.org/10.1090/S0273-0979-03-00988-1>
- J. Hofbauer, Deterministic evolutionary game dynamics, in *Evolutionary Game Dynamics*, Proc. Sympos. Appl. Math. 69, Amer. Math. Soc., 2011, 61–79. <https://doi.org/10.1090/psapm/069/2882634>
- Original result: R. Cressman, Local stability for smooth selection dynamics for normal form games, Math. Social Sci. 34 (1997), 1–19. The statement follows its restatement in Hofbauer and Sigmund (2003).
