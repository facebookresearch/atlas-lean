# A square-root oracle factors pq on exactly half of the units

Let $p \ne q$ be primes with $q$ odd, $n = pq$, and let $O : \mathbb{Z}/n\mathbb{Z} \to \mathbb{Z}/n\mathbb{Z}$
be any function with $O(k^2)^2 = k^2$ for every unit $k$ (a deterministic algorithm returning one
square root of each square of a unit). Then

$$2 \cdot \#\{k \in (\mathbb{Z}/n\mathbb{Z})^\times : \gcd(k - O(k^2), n) \in \{p, q\}\} = \varphi(n).$$

So the trial "draw a uniform unit $k$, ask the oracle for a square root $k_1$ of $k^2$, output
$\gcd(k - k_1, n)$" factors $n$ with probability exactly $1/2$, for every oracle. Independent trials
fail $t$ times in a row with probability $2^{-t}$.

The proof pairs $k$ with $ck$, where $c \equiv 1 \pmod p$ and $c \equiv -1 \pmod q$. Both have the
same square, hence the same answer $k_1$; they agree modulo $p$, and since $k_1 \equiv \pm k
\pmod q$, exactly one of $k - k_1$ and $ck - k_1$ vanishes modulo $q$. So exactly one of the two
succeeds.

## Comparison with the source

Rabin's Theorem 1 says that a square-root algorithm taking $F(n)$ steps yields a factoring
algorithm taking $2F(n) + 2\log_2 n$ expected steps; its proof rests on the statement here
(exactly four square roots of $k^2$, all equally likely, two of which give a factor). Rabin takes $p$ and $q$ to be (large) primes and draws $0 < k < n$, discarding
the negligible non-units; the statement here requires only $q$ odd and draws units. The count
behind Rabin's Theorem 2, for an algorithm that succeeds on a fraction $1/e$ of the squares, is
[A partial square-root oracle factors pq on half of its domain](two-mul-card-gcd-mem-eq-card.md),
from which this theorem is derived.

## Informally uses

- [A partial square-root oracle factors pq on half of its domain](two-mul-card-gcd-mem-eq-card.md):
  the case where the oracle answers on every square.

## Background

- [Inverting the Rabin function extracts square roots](rabin-function-two-mul.md): why the
  theorem makes inverting the Rabin function as hard as factoring.

## Sources

- M. O. Rabin, *Digitalized signatures and public-key functions as intractable as factorization*, MIT/LCS/TR-212, MIT Laboratory for Computer Science, January 1979, Section 4, Theorem 1 and its proof (pp. 12–13), and Theorem 2 (p. 14).
