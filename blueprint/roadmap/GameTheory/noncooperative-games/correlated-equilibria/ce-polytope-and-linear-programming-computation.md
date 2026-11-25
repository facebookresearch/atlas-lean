# CE polytope and linear-programming computation

Let a finite game with nonempty finite strategy sets have rational payoffs given explicitly. Its
[correlated equilibria](is-correlated-eq.md), with costs $c_i = -u_i$ and $\varepsilon = 0$, are the probability
distributions $\sigma$ on strategy profiles satisfying, for every player $i$ and all $s_i, s'_i$,
$\sum_{s_{-i}} \sigma(s_i, s_{-i}) (u_i(s_i, s_{-i}) - u_i(s'_i, s_{-i})) \ge 0$. They form a polytope, cut out of the simplex of
distributions by $\sum_i \lvert S_i \rvert^2$ linear inequalities; it is [convex](convex-set-of-is-correlated-eq.md)
and nonempty, since [Nash's theorem](../nash-s-theorem/exists-is-mixed-nash.md) gives a mixed Nash equilibrium and
[its product distribution is a correlated equilibrium](is-correlated-eq-product-dist-of-is-mixe.md). Consequently a
correlated equilibrium maximizing a rational linear objective is computable by linear programming in time polynomial in the bit size of
the explicit normal form; that size is exponential in the number of players when every player has at least two strategies.

## Expansion

This node states a precise result. A good expansion adds a page for the pending prerequisite below and links it under the dependency sections.

- Proof prerequisite: an optimal solution of a feasible, bounded linear program with rational data is computable in time polynomial in its bit size (Khachiyan's ellipsoid method with the standard bit-size bounds); [Linear programming is in P (Khachiyan)](../../../TheoryOfComputation/polynomial-time-problems/linear-programming-feasibility/lp-in-p.md) states only the feasibility decision.

## Depends on

- [Correlated equilibrium](is-correlated-eq.md)
- [Gain from a switched recommendation](switch-gain.md)

## Proof depends on

- [The set of correlated equilibria is convex](convex-set-of-is-correlated-eq.md)
- [Nash's theorem](../nash-s-theorem/exists-is-mixed-nash.md)
- [Mixed Nash equilibria are correlated equilibria](is-correlated-eq-product-dist-of-is-mixe.md)
- [Linear programming is in P (Khachiyan)](../../../TheoryOfComputation/polynomial-time-problems/linear-programming-feasibility/lp-in-p.md)

## Sources

- A. X. Jiang and K. Leyton-Brown, *Polynomial-time Computation of Exact Correlated Equilibrium in Compact Games* (arXiv:1011.0253v1; Games Econ. Behav. 2015), §1 (the correlated-equilibrium linear feasibility program has size polynomial in the normal form, which grows exponentially in the number of players) and §2, Definition 2.1 with constraints (1) and (2). <https://arxiv.org/pdf/1011.0253>
- Computing Correlated Equilibria in Multi-Player Games — Papadimitriou and Roughgarden. <https://ranger.uta.edu/~weems/NOTES6319/PAPERSONE/papadimitriou.pdf> Background reference.
- CS364A Lecture #18: From External Regret to Swap Regret and the Minimax Theorem — Tim Roughgarden, Stanford University (2013). <http://theory.stanford.edu/~tim/f13/l/l18.pdf> Background reference.
