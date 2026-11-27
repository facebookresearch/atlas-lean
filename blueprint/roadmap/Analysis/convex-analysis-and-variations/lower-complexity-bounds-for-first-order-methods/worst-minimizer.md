# Minimiser of the worst function

For $n, m \in \mathbb{N}$, the vector $\bar x \in \mathbb{R}^n$ with

$$
\bar x^{(j)} = 1 - \frac{j}{m + 1} \quad (1 \le j \le m), \qquad \bar x^{(j)} = 0 \quad (j > m).
$$

For $1 \le m \le n$ it solves $A_m x = e_1$, so for $L \ge 0$ it minimises the convex quadratic
[worst function](worst-function.md) $f_m$ (see [its minimum value](worst-function-worst-minimizer.md)).
For $n > m$ the minimiser is not unique: any vector agreeing with $\bar x$ on the first $m$
coordinates is also one.

## Sources

- Yu. Nesterov, *Introductory Lectures on Convex Programming, Volume I: Basic course*, lecture notes, July 2, 1998 (draft of the 2004 Kluwer book *Introductory Lectures on Convex Optimization: A Basic Course*; the numbering cited here is that of the 1998 draft), Section 2.1.2: the solution $\bar x_k$ of $f_k'(x) = 0$, which defines this vector.
