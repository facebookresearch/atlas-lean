# Randomized rounding for MAX-SAT

Goemans and Williamson (*SIAM J. Discrete Math.* 7(4) (1994)) give a $\frac34$-approximation for
weighted MAX SAT from two simple randomized algorithms. Johnson's assignment sets each variable
true with probability $\frac12$ and satisfies a $k$-literal clause with probability $1 - 2^{-k}$.
Randomized rounding solves the linear relaxation (LP), with variables $y_i$ for the literals and
$z_j$ for the clauses, and sets $x_i$ true with probability $y_i$; by the arithmetic–geometric
mean inequality it satisfies clause $j$ with probability at least $\beta_k z_j$,
$\beta_k = 1 - (1 - 1/k)^k$ (Lemma 3.1). Since $(1 - 2^{-k}) + \beta_k \ge \frac32$ for every $k$, the
better of the two has expected weight at least $\frac34 Z^*_{LP} \ge \frac34 \mathrm{OPT}$
(Theorem 4.1).

The pages below state, for clauses whose literals use distinct variables, Johnson's bound,
Lemma 3.1, Theorem 4.1 and the comparison with the MAX SAT optimum, with the satisfaction
probability of a clause in closed form, which equals the probability under independent rounding.
Distinct variables matter: for $x_0 \vee x_0$ with $p_0 = \frac12$ the closed form is $\frac34$,
while the clause is satisfied with probability $\frac12$. Section 5 of the paper gives further
$\frac34$-approximation algorithms, which set each variable true with probability $f(y_i)$ for
suitable functions $f$.

- [Probability that a literal is true](literal-prob.md)
- [Satisfaction probability of a clause](clause-sat-prob.md)
- [The closed form is the satisfaction probability](clause-sat-prob-eq-sum-assignments.md)
- [Johnson's random assignment](clause-sat-prob-half.md)
- [Johnson's probabilities are probabilities](half-mem-icc.md)
- [Left-hand side of the clause constraint of the MAX SAT relaxation](lp-clause-bound.md)
- [Feasible solutions of the MAX SAT linear relaxation](lpfeasible.md)
- [The randomized-rounding factor](rounding-factor.md)
- [Goemans–Williamson Lemma 3.1](rounding-factor-mul-le-clause-sat-prob.md)
- [The per-clause inequality behind the 3/4 guarantee](three-halves-le-johnson-add-rounding-fac.md)
- [Goemans–Williamson Theorem 4.1, per clause](three-quarters-mul-le-average.md)
- [Expected weight of a randomized assignment](expected-weight.md)
- [Goemans–Williamson Theorem 4.1](three-quarters-le-max-expected-weight.md)
- [Weight satisfied by a truth assignment](satisfied-weight.md)
- [Truth assignments are feasible for the relaxation](lp-feasible-of-assignment.md)
- [The 3/4 guarantee against the MAX SAT optimum](three-quarters-le-max-expected-weight-of.md)

## Related topics

- [Maximum satisfiability](../../../TheoryOfComputation/np-completeness/satisfiability/maximum-satisfiability/README.md):
  NP-completeness of the problem being approximated.
- [Approximability of MAX-3SAT](../../../TheoryOfComputation/pcp-and-inapproximability/approximability-of-max-3sat/README.md):
  Håstad's theorem that $\frac78$ is optimal for MAX 3SAT, the hardness side of these guarantees.
- [Goemans–Williamson MAX-CUT algorithm](../goemans-williamson-max-cut-algorithm/README.md): the
  semidefinite successor, which also gives a $0.758$-approximation for MAX SAT (J. ACM 1995, §7).
