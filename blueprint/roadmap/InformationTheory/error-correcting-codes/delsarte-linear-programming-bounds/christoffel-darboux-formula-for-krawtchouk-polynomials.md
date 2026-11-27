# Christoffel-Darboux formula for Krawtchouk polynomials

For $x \ne y$ and $0 \le t < n$,

$$
\sum_{k=0}^{t} \frac{K_k(x) K_k(y)}{\binom{n}{k}} = \frac{t+1}{2\binom{n}{t}} \cdot \frac{K_{t+1}(x)K_t(y) - K_t(x)K_{t+1}(y)}{y - x} .
$$

## Proof sketch

Multiply the three-term recurrence for $K_k(x)$ by $K_k(y)/\binom{n}{k}$, subtract the same with $x$ and $y$ exchanged, and telescope the sum over $k$; the factor $n - 2x$ versus $n - 2y$ produces $2(y - x)$.

## Depends on

- [Binary Krawtchouk polynomials](binary-krawtchouk-polynomials.md)

## Proof depends on

- [Orthogonality of Krawtchouk polynomials](orthogonality-of-krawtchouk-polynomials.md)

## Sources

- Robert J. McEliece, Eugene R. Rodemich, Howard Rumsey Jr., Lloyd R. Welch, "New upper bounds on the rate of a code via the Delsarte-MacWilliams inequalities", IEEE Transactions on Information Theory 23(2) (1977).
- Vladimir I. Levenshtein, "Krawtchouk polynomials and universal bounds for codes and designs in Hamming spaces", IEEE Transactions on Information Theory 41(5) (1995).
