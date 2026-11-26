# Delsarte inequalities for distance distributions

For every nonempty $C \subseteq \{0,1\}^n$ and every $0 \le k \le n$,

$$
\sum_{i=0}^{n} A_i\, K_k(i) \ \ge\ 0 .
$$

For linear codes $\frac{1}{|C|}\sum_i A_i K_k(i)$ equals the number of weight-$k$ words of the dual code (MacWilliams identity).

## Proof sketch

$|C| \sum_i A_i K_k(i) = \sum_{x, x' \in C}\sum_{|y| = k}(-1)^{(x + x')\cdot y} = \sum_{|y| = k}\Big|\sum_{x \in C}(-1)^{x\cdot y}\Big|^2 \ge 0$.

## Depends on

- [Distance distribution of a binary code](distance-distribution-of-a-binary-code.md)
- [Binary Krawtchouk polynomials](binary-krawtchouk-polynomials.md)

## Proof depends on

- [MacWilliams identity](../macwilliams-identity.md)

## Sources

- Philippe Delsarte, "An algebraic approach to the association schemes of coding theory", Philips Research Reports Supplements 10 (1973) (historical attribution).
- Robert J. McEliece, Eugene R. Rodemich, Howard Rumsey Jr., Lloyd R. Welch, "New upper bounds on the rate of a code via the Delsarte-MacWilliams inequalities", IEEE Transactions on Information Theory 23(2) (1977) 157-166, https://doi.org/10.1109/TIT.1977.1055688.
