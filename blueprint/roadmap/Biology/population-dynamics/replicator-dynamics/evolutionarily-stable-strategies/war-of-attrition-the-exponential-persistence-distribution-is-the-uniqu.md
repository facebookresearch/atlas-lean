# War of attrition: the exponential strategy

In Maynard Smith's (1974, Sec. 3) war of attrition each contestant chooses a cost $m \ge 0$ it is prepared to pay; if $m_1 > m_2$ the first gets $v - m_2$ and the second $-m_2$, and ties are split by a small random perturbation. No pure strategy is evolutionarily stable: against a strategy playing $m_1$ the mutant $m_1 + \varepsilon$ does better, and if $m_1 > v/2$ the mutant $0$ does better still. Choosing a density $p$ so that a fixed $m$ earns the same against it for all $m$ gives $v\,p(m) = 1 - \int_0^m p(x)\, dx$ (his eq. (3)), solved by the exponential strategy $I$ with density $p(x) = \frac1v e^{-x/v}$ (eq. (4)); every pure $m$ earns $E(m, I) = 0$ against it. Maynard Smith checks stability against pure mutants $J = m$: $E_J(I) - E_J(J) = 2v e^{-m/v} - 3v/2 + m > 0$ for all $m > 0$ (eq. (5)), so no pure mutant can invade $I$. Eq. (5) covers pure mutants only; that $I$ is also stable against mixed mutants, and so an ESS, and that it is the unique ESS of the game, is the general result of Bishop and Cannings (1978). With costs incurred at rate $c$ per unit display time, the persistence time $m/c$ is exponential with mean $v/c$.

## Expansion

1. The game: strategies as laws on $[0, \infty)$, payoffs with the tie convention, and the ESS conditions for mixed strategies on a continuum.
2. Nonexistence of a pure ESS.
3. The equal-payoff property of the exponential strategy, $E(m, I) = 0$ for all $m \ge 0$, from eq. (3).
4. Stability against pure mutants (eq. (5)), and against all mixed mutants with uniqueness (Bishop and Cannings).

## Sources

- J. Maynard Smith, The theory of games and the evolution of animal conflicts, J. Theor. Biol. 47 (1974), 209–221, Sec. 3, eqs. (2)–(5). <https://doi.org/10.1016/0022-5193(74)90110-6>
- Original result: D. T. Bishop and C. Cannings, A generalized war of attrition, J. Theor. Biol. 70 (1978), 85–124. <https://doi.org/10.1016/0022-5193(78)90304-1>
