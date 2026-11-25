# Approximation algorithms and approximation ratios

The two ratio conventions for maximization are equivalent. For a real threshold $\alpha>0$,
write $\beta=1/\alpha$. For any real values $O$ and $V$,

$$
\alpha\le1\;\text{ and }\;\alpha O\le V
\quad\Longleftrightarrow\quad
1\le\beta\;\text{ and }\;O/\beta\le V.
$$

In an approximation guarantee, $O$ is the optimum and $V$ is the value attained by the solver
or its expected value. The equivalence also holds at $O=0$: only the approximation parameter
is inverted. For example, a $1/2$-approximation in the threshold convention is a $2$-approximation
in the factor convention.

## Background

Consider bitstring instances $x$ and bitstring candidate solutions $s$, with a nonnegative
rational objective $v(x,s)$. Each instance has at least one feasible solution. A polynomial
bound on feasible solution lengths makes this set finite, so the optimum is attained. The
objective and ratios are part of the specification; the solver need not compute them.

A deterministic solver runs in polynomial time and returns a feasible solution on every
instance. A [minimization guarantee](is-min-approximation.md) bounds its cost above by
$\alpha\,\mathrm{OPT}(x)$ with $\alpha\ge1$. A [maximization guarantee](is-max-approximation.md)
bounds its value below by $\alpha\,\mathrm{OPT}(x)$ with $0<\alpha\le1$. Equivalently, use the
same inequality against every feasible value.

For [randomized minimization](is-randomized-min-approximation.md) or
[randomized maximization](is-randomized-max-approximation.md), the solver is polynomial time on
the encoded pair of the instance and a fair tape whose length is given by a fixed polynomial.
Every tape must return a feasible solution. The [expected value](expected-value.md) is the
uniform average over the tapes, counting tapes separately when their outputs coincide. For
example, independent fair assignments satisfy each nonempty MAX SAT clause with probability
at least $1/2$, so the expected number satisfied is at least half the optimum.

A [polynomial-time approximation scheme](../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-ptas.md)
provides guarantees arbitrarily close to exact optimization rather than one fixed ratio. At a
fixed precision, [the maximization guarantee](approx-at-iff-is-max-approximation.md) is equivalent
to the scheme's guarantee at that precision, with the same positive rational threshold and a
polynomial-time specialized solver.

## Sources

- D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*, Cambridge University Press, 2011, electronic edition <http://www.designofapproxalgs.com/book.pdf>, Section 1.1: Definition 1.1 ($\alpha$-approximation algorithms, with the performance guarantee also called the approximation ratio or factor, and the convention $\alpha > 1$ for minimization and $\alpha < 1$ for maximization) and Definition 1.2 (polynomial-time approximation schemes); Theorem 1.17 and Theorem 5.1 (randomized approximation algorithms, judged by the expected value of the solution).
