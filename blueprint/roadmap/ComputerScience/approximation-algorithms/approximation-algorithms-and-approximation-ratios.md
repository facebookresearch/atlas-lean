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
at least $1/2$, so the expected number satisfied is at least half the optimum. Every assignment
is feasible in MAX SAT; in contrast, the randomized set-cover algorithm in Theorem 1.17 of
Williamson and Shmoys produces a feasible cover only with high probability.

A [polynomial-time approximation scheme](../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-ptas.md)
provides guarantees arbitrarily close to exact optimization rather than one fixed ratio. For
one fixed unary precision $k$, the [fixed-precision equivalence](approx-at-iff-is-max-approximation.md)
identifies `ApproxAt` at a rational threshold $0<\alpha\le1$ with the deterministic maximization
guarantee for $x\mapsto A(x,1^k)$, provided this specialized solver is polynomial time. It does
not characterize `IsPTAS`, which additionally requires NPO and a polynomial-time pair-input
solver for every $k\ge1$, possibly a different solver at each $k$. Its schedule $1-1/k$ gives a
positive threshold for $k\ge2$, but is $0$ at $k=1$ and is then outside the equivalence.

## Sources

- D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*, Cambridge University Press, 2011, [electronic edition](https://www.designofapproxalgs.com/book.pdf), §1.1, Definitions 1.1–1.2 (approximation guarantees and schemes); Theorem 5.1 (MAX SAT guarantee in expectation) and Theorem 1.17 (set-cover guarantee with feasibility only with high probability).
