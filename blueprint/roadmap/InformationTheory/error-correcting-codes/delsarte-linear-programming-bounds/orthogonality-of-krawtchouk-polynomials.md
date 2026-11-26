# Orthogonality of Krawtchouk polynomials

For $0 \le k, l \le n$,

$$
\sum_{i=0}^{n} \binom{n}{i} K_k(i) K_l(i) = 2^{n} \binom{n}{k}\, \delta_{kl},
$$

and $\binom{n}{i}K_k(i) = \binom{n}{k}K_i(k)$. The $K_k$ satisfy the three-term recurrence $(k+1)K_{k+1}(x) = (n - 2x)K_k(x) - (n - k + 1)K_{k-1}(x)$.

## Proof sketch

Using the character formula, $\sum_x K_k(|x|)K_l(|x|) = \sum_{|y| = k, |y'| = l}\sum_x (-1)^{x\cdot(y + y')}$, and the inner sum is $2^n$ if $y = y'$ and $0$ otherwise. Grouping $x$ by weight gives orthogonality; the symmetry relation is double counting and the recurrence follows from the generating function $\sum_k K_k(x) z^k = (1 - z)^{x}(1 + z)^{n - x}$.

## Depends on

- [Binary Krawtchouk polynomials](binary-krawtchouk-polynomials.md)

## Sources

- F. J. MacWilliams, N. J. A. Sloane, "The Theory of Error-Correcting Codes", North-Holland (1977).
- Vladimir I. Levenshtein, "Krawtchouk polynomials and universal bounds for codes and designs in Hamming spaces", IEEE Transactions on Information Theory 41(5) (1995).
