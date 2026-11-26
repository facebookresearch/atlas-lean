# Asymptotics of the smallest root of Krawtchouk polynomials

Let $x_1(t)$ be the smallest root of $K_t$ (all roots are real, simple and lie in $(0, n)$). If $t/n \to \tau \in (0, 1/2]$, then

$$
\frac{x_1(t)}{n} \to \frac12 - \sqrt{\tau(1 - \tau)} .
$$

## Proof sketch

Real-rootedness and interlacing of consecutive Krawtchouk polynomials follow from orthogonality. The asymptotic location of the extreme zero follows from the three-term recurrence viewed as a tridiagonal (Jacobi) matrix whose largest eigenvalue determines $n - 2x_1$, estimated by a Rayleigh quotient with test vectors and Gershgorin-type bounds, giving $n - 2x_1 \approx 2\sqrt{t(n - t)}$.

## Depends on

- [Binary Krawtchouk polynomials](binary-krawtchouk-polynomials.md)

## Proof depends on

- [Orthogonality of Krawtchouk polynomials](orthogonality-of-krawtchouk-polynomials.md)

## Sources

- Robert J. McEliece, Eugene R. Rodemich, Howard Rumsey Jr., Lloyd R. Welch, "New upper bounds on the rate of a code via the Delsarte-MacWilliams inequalities", IEEE Transactions on Information Theory 23(2) (1977).
- Vladimir I. Levenshtein, "Krawtchouk polynomials and universal bounds for codes and designs in Hamming spaces", IEEE Transactions on Information Theory 41(5) (1995).
