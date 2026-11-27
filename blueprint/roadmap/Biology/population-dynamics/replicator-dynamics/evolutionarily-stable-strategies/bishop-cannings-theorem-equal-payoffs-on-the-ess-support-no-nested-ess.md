# Bishop–Cannings and Haigh conditions for evolutionarily stable strategies

Let $A = (a_{ij})$ be the payoff matrix of a finite symmetric game, with mixed strategies $p$ in the simplex and $E(p, q) = p\cdot Aq$; $p$ is an ESS if $E(p, p) \ge E(q, p)$ for all $q$ and $E(p, q) > E(q, q)$ whenever $q \ne p$ and $E(p, p) = E(q, p)$ (Haigh's appendix to Maynard Smith 1974, (A1)–(A2)). (a) Equal-payoff property: if $p$ is an ESS, then $(Ap)_i = \max_j (Ap)_j = p\cdot Ap$ for every $i$ with $p_i > 0$ (Haigh, Theorem 3); equivalently, every pure or mixed strategy supported in the support of $p$ earns the same payoff $E(p, p)$ against $p$ (the Bishop–Cannings theorem; Bishop and Cannings 1978; Maynard Smith 1982, appendix on the Bishop–Cannings theorem). (b) If $p$ is an ESS and $q \ne p$ has support contained in that of $p$, then $q$ is not an ESS: by (a), $E(q, p) = E(p, p)$, so $E(p, q) > E(q, q)$, which violates the first condition for $q$. Hence the supports of the ESSs of a game are pairwise incomparable and there are finitely many ESSs. (c) Since $(p - q)\cdot A(p - q) = (p\cdot Ap - q\cdot Ap) - (p\cdot Aq - q\cdot Aq)$ (Haigh), an ESS $p$ satisfies $(p - q)\cdot A(p - q) < 0$ for every $q \ne p$ with $q\cdot Ap = p\cdot Ap$, in particular for every $q \ne p$ supported in the support of $p$.

## Depends on

- [Evolutionarily stable state of a matrix game](../../stability-of-evolutionarily-stable-states/is-ess.md)

## Proof depends on

- [An evolutionarily stable state is a Nash equilibrium](../../stability-of-evolutionarily-stable-states/is-nash-2.md)

## Expansion

1. Finite symmetric games, mixed strategies, Nash equilibria and ESSs.
2. The equal-payoff property from the first ESS condition (Haigh's Theorem 3), and its form for strategies on a continuum (Bishop and Cannings).
3. The support property and the finiteness of the set of ESSs.
4. The negative-definiteness condition on the face of the support, and its converse for regular Nash equilibria ($(Ap)_i < p\cdot Ap$ off the support), as a separate statement.
5. Haigh's three-strategy example with no ESS.

## Sources

- J. Maynard Smith, The theory of games and the evolution of animal conflicts, J. Theor. Biol. 47 (1974), 209–221, Appendix by J. Haigh, (A1)–(A2), Theorems 1–3 and the identity before Theorem 3. <https://doi.org/10.1016/0022-5193(74)90110-6>
- J. Maynard Smith, *Evolution and the Theory of Games*, Cambridge University Press, 1982, appendix on the Bishop–Cannings theorem. <https://doi.org/10.1017/CBO9780511806292>
- Original result: D. T. Bishop and C. Cannings, A generalized war of attrition, J. Theor. Biol. 70 (1978), 85–124. <https://doi.org/10.1016/0022-5193(78)90304-1>
- M. Broom, C. Cannings and G. T. Vickers, Multi-player matrix games, Bull. Math. Biol. 59 (1997), 931–952, Section 2.1 and Theorem 2.2.3. <https://doi.org/10.1007/BF02460000>
- J. Hofbauer and K. Sigmund, Evolutionary game dynamics, Bull. Amer. Math. Soc. 40 (2003), 479–519, eqs. (16)–(17) and Section 2.3.
