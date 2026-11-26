# Arithmetic in the ring of polynomials modulo X^r - 1 and n

Represent an element of $R_{n,r} = (\mathbb{Z}/n\mathbb{Z})[X]/(X^r - 1)$ by its $r$ coefficients in $\{0, \dots, n-1\}$. On a word RAM with $2^w > n^2 + n$:

1. multiplication in $R_{n,r}$ by the schoolbook rule (add $p_i q_j$ into coefficient $(i + j) \bmod r$, reducing mod $n$ after each addition) uses $O(r^2)$ instructions;
2. computing $p^e$ by repeated squaring uses $O(r^2 \log(e + 2))$ instructions;
3. writing the coefficients of $X^e + a$ and testing two elements for equality use $O(r)$ instructions.

## Proof sketch

All intermediate values stay below $n^2 + n$. Repeated squaring keeps the invariant that $R \cdot B^e$ is unchanged while $e$ is halved, so it performs $O(\log e)$ multiplications.

## Depends on

- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- M. Agrawal, N. Kayal and N. Saxena, "PRIMES is in P", Annals of Mathematics 160(2), 2004.
- D. E. Knuth, "The Art of Computer Programming, Volume 2: Seminumerical Algorithms", 3rd ed., Addison-Wesley, 1997, Sections 4.6 and 4.6.3.
