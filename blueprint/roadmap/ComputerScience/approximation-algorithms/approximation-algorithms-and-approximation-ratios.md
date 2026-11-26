# Approximation algorithms and approximation ratios

Consider bitstring instances $x$ and candidate solutions $s$, with a nonnegative rational objective $v(x,s)$. Each instance has at least one feasible solution, and a polynomial bound on feasible solution lengths makes the feasible set finite. Thus $\mathrm{OPT}(x)$ is attained: it is the minimum feasible cost or maximum feasible value, according to the direction of optimization.

An approximation algorithm runs in polynomial time and returns a feasible solution on every instance. Its performance guarantee of ratio $\alpha$ bounds the value $V$ it achieves:

- For minimization, $\alpha\ge 1$ and $V\le\alpha\,\mathrm{OPT}(x)$.
- For maximization, $0<\alpha\le 1$ and $\alpha\,\mathrm{OPT}(x)\le V$.

The exact case $\alpha=1$ is included. Equivalently, the appropriate inequality compares the achieved value with every feasible value. The objective and ratio are part of the specification, not quantities the solver must compute.

For a deterministic solver, $V=v(x,A(x))$. For a randomized solver, the run time is polynomial on the encoded pair of the instance and a fair bit tape of polynomial length in the instance length. Every allowed tape must yield a feasible solution. Here $V$ is the expected objective value, the uniform average over tapes, counting two tapes separately even when they yield the same solution.

## Background

For deterministic or randomized maximization, the same guarantee can use a factor $\beta=1/\alpha\ge1$ in place of the threshold $\alpha$: require $\mathrm{OPT}(x)/\beta\le V$ with the same time and feasibility requirements. A $1/2$-approximation in the threshold convention is a $2$-approximation in the factor convention. The optimum is never a divisor, so the equivalence includes a zero optimum.

For example, independent fair assignments satisfy each nonempty MAX SAT clause with probability at least $1/2$, so the expected number satisfied is at least half the optimum. Every assignment is feasible in MAX SAT; in contrast, the randomized set-cover algorithm in Theorem 1.17 of Williamson and Shmoys produces a feasible cover only with high probability.

A [polynomial-time approximation scheme](../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-ptas.md) provides guarantees arbitrarily close to exact optimization rather than one fixed ratio. For one fixed unary precision $k$, the [fixed-precision equivalence](approx-at-iff-is-max-approximation.md) identifies `ApproxAt` at a rational threshold $0<\alpha\le1$ with the deterministic maximization guarantee for $x\mapsto A(x,1^k)$, provided this specialized solver is polynomial time. It does not characterize `IsPTAS`, which additionally requires NPO and a polynomial-time pair-input solver for every $k\ge1$, possibly a different solver at each $k$. Its schedule $1-1/k$ gives a positive threshold for $k\ge2$, but is $0$ at $k=1$ and is then outside the equivalence.

- [Integrality gaps of linear programming relaxations](lp-based-approximation/integrality-gaps-of-linear-programming.md)

## Sources

- D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*, Cambridge University Press, 2011, [electronic edition](https://www.designofapproxalgs.com/book.pdf), §1.1, Definitions 1.1–1.2 (deterministic guarantees and schemes); Chapter 5, opening paragraph, p. 105 (guarantees in expectation); Theorem 5.1 (MAX SAT example); Theorem 1.17 (contrast: feasibility only with high probability).
