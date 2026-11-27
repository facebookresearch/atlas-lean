# Approximation algorithms and approximation ratios

Consider an optimization problem in which each instance $I$ has a nonempty set of feasible solutions, each solution $s$ has a nonnegative value $f(s)$, and $\mathrm{OPT}(I)$ is the minimum value, for a *minimization* problem, or the maximum value, for a *maximization* problem.

An *$\alpha$-approximation algorithm* is a polynomial-time algorithm that, on every instance $I$, returns a feasible solution $A(I)$ whose value is within a factor $\alpha$ of optimal. The number $\alpha$ is its *performance guarantee*, also called its *approximation ratio* or *approximation factor*. Under the convention used here:
- for minimization, $\alpha \ge 1$ and $f(A(I)) \le \alpha \cdot \mathrm{OPT}(I)$;
- for maximization, $0 < \alpha \le 1$ and $f(A(I)) \ge \alpha \cdot \mathrm{OPT}(I)$.

Some authors instead use $\alpha \ge 1$ for maximization and require $f(A(I)) \ge \mathrm{OPT}(I)/\alpha$. Under that convention, a $1/2$-approximation here is a $2$-approximation there.

A *randomized* $\alpha$-approximation algorithm runs in polynomial time and satisfies the bound in expectation: $\mathbb{E}[f(A(I))] \le \alpha \cdot \mathrm{OPT}(I)$ for minimization, or $\ge$ for maximization. For example, setting each variable of a MAX SAT instance to true independently with probability $1/2$ is a randomized $1/2$-approximation.

A family of algorithms with ratio $1 + \varepsilon$, or $1 - \varepsilon$ for maximization, for every $\varepsilon > 0$ is a [polynomial-time approximation scheme](../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-ptas.md).

## Background

- [Polynomial-time approximation schemes](../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-ptas.md)
- [Integrality gaps of linear programming relaxations](lp-based-approximation/integrality-gaps-of-linear-programming.md)

## Sources

- D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*, Cambridge University Press, 2011, electronic edition <http://www.designofapproxalgs.com/book.pdf>, Section 1.1: Definition 1.1 ($\alpha$-approximation algorithms, with the performance guarantee also called the approximation ratio or factor, and the convention $\alpha > 1$ for minimization and $\alpha < 1$ for maximization) and Definition 1.2 (polynomial-time approximation schemes); Theorem 1.17 and Theorem 5.1 (randomized approximation algorithms, judged by the expected value of the solution).
