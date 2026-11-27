# Closed formula for bifence-free fence tilings

Let $a$, $b$ be nonzero elements of a field
and let $\xi(n) = n \bmod 2$. For every natural number $n$, the weighted number $C_n$ of tilings of
the $n$-board by half-squares and $(1/2, 1/2)$-fences with no bifence, with half-square weights
$a$ and $b$, is

$$
C_n = \left(\frac{a}{b}\right)^{\xi(n)}
\sum_{i=0}^{\lfloor 2n/3 \rfloor} \binom{2n-2i}{i} (ab)^{n-i}.
$$

## Sources

- Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024, Lemma 3.15.
