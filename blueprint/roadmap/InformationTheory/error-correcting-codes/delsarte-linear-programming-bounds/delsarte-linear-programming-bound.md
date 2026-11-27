# Delsarte's linear programming bound

Let $A(n, d)$ be the maximum size of a binary code of length $n$ and minimum distance $d$. Then $A(n, d) \le \mathrm{LP}(n, d)$, the optimum of

$$
\max\ 1 + \sum_{i=d}^{n} A_i \quad \text{s.t.} \quad A_i \ge 0, \quad \binom{n}{k} + \sum_{i=d}^{n} A_i K_k(i) \ge 0 \ \ (0 \le k \le n).
$$

Dually, if $f(x) = \sum_{k=0}^{n} f_k K_k(x)$ has $f_0 > 0$, $f_k \ge 0$ for $k \ge 1$, and $f(i) \le 0$ for $d \le i \le n$, then $A(n, d) \le f(0)/f_0$.

## Proof sketch

The distance distribution of an optimal code is feasible by the Delsarte inequalities (with $A_0 = 1$ and $A_1 = \dots = A_{d-1} = 0$), and its objective is $|C|$. For the dual form, $f(0) + \sum_{i \ge d} A_i f(i) = \sum_k f_k \sum_i A_i K_k(i) \ge f_0 \sum_i A_i K_0(i) = f_0 |C|$, while the left side is at most $f(0)$.

## Depends on

- [Binary Krawtchouk polynomials](binary-krawtchouk-polynomials.md)

## Proof depends on

- [Delsarte inequalities for distance distributions](delsarte-inequalities.md)
- [Orthogonality of Krawtchouk polynomials](orthogonality-of-krawtchouk-polynomials.md)

## Sources

- Philippe Delsarte, "An algebraic approach to the association schemes of coding theory", Philips Research Reports Supplements 10 (1973) (historical attribution).
- Robert J. McEliece, Eugene R. Rodemich, Howard Rumsey Jr., Lloyd R. Welch, "New upper bounds on the rate of a code via the Delsarte-MacWilliams inequalities", IEEE Transactions on Information Theory 23(2) (1977) 157-166, https://doi.org/10.1109/TIT.1977.1055688.
