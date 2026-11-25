# Zero-sum value as a linear program

Let $A$ be a real $m \times n$ matrix with $m, n \ge 1$, the payoff to the row player. The value $v = \max_{p \in \Delta_m} \min_{q \in \Delta_n} p^{\mathsf T} A q$
equals the optimum of the linear program "maximize $t$ subject to $p \in \Delta_m$ and $(A^{\mathsf T} p)_j \ge t$ for all $j$", whose dual is the
column player's program "minimize $w$ subject to $q \in \Delta_n$ and $(Aq)_i \le w$ for all $i$"; by strong duality the two optima agree,
and optimal solutions are optimal mixed strategies. No integrality assumption is needed. If $A$ has rational entries in binary, the value
and optimal strategies are computable in polynomial time by linear programming.

## Expansion

This node states a precise result. A good expansion adds a page for the pending prerequisite below and links it under the dependency sections.

- Proof prerequisite: an optimal solution of a feasible, bounded linear program with rational data is computable in time polynomial in its bit size (Khachiyan's ellipsoid method with the standard bit-size bounds); [Linear programming is in P (Khachiyan)](../../../TheoryOfComputation/polynomial-time-problems/linear-programming-feasibility/lp-in-p.md) states only the feasibility decision.

## Proof depends on

- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md)
- [Linear programming is in P (Khachiyan)](../../../TheoryOfComputation/polynomial-time-problems/linear-programming-feasibility/lp-in-p.md)

## Related topics

- [Saddle point of a matrix game](matrix-game-exists-is-saddle-point-on.md)
- [Von Neumann's minimax theorem](matrix-game-minimax.md)

## Sources

- T. Roughgarden, CS261 Lecture #10: The Minimax Theorem and Algorithms for Linear Programming, Stanford University (2016), §1.4 (the row and column players' linear programs, their duality and the value) and §2 (polynomial-time solvability of linear programs). <http://timroughgarden.org/w16/l/l10.pdf>
