# A partial square-root oracle factors pq on half of its domain

Let $p \ne q$ be primes with $q$ odd, $n = pq$, $Q$ a set of residues modulo $n$, and let
$O : \mathbb{Z}/n\mathbb{Z} \to \mathbb{Z}/n\mathbb{Z}$ be any function with $O(k^2)^2 = k^2$ for every unit
$k$ with $k^2 \in Q$. Then

$$2 \cdot \#\{k \in (\mathbb{Z}/n\mathbb{Z})^\times : k^2 \in Q,\ \gcd(k - O(k^2), n) \in \{p, q\}\}
  = \#\{k \in (\mathbb{Z}/n\mathbb{Z})^\times : k^2 \in Q\}.$$

The oracle may return anything outside $Q$. The proof is the pairing $k \leftrightarrow ck$ of
[A square-root oracle factors pq on exactly half of the units](two-mul-card-gcd-mem-eq-totient.md),
which preserves $k^2$ and hence the condition $k^2 \in Q$; that theorem is the case where $Q$ is
everything.

## Comparison with the source

Rabin's Theorem 2: if an algorithm finds square roots in $F(n)$ steps for a fraction $1/e$ of the
squares of units, then $n$ can be factored in $2eF(n) + 2\log_2 n$ expected steps. Its proof uses
that among the trials whose square lands where the algorithm succeeds, half produce a factor; that
count is the statement here, with $Q$ the set of squares on which the algorithm succeeds. Each
trial then succeeds with probability $\#\{k : k^2 \in Q\}/(2\varphi(n))$, which is $1/(2e)$ when $Q$
is a fraction $1/e$ of the squares of units (each square of a unit has exactly four roots).

## Informally uses

- [The gcd with pq is a prime factor exactly when one prime divides](gcd-mul-mem-iff.md).

## Sources

- M. O. Rabin, *Digitalized signatures and public-key functions as intractable as factorization*, MIT/LCS/TR-212, MIT Laboratory for Computer Science, January 1979, Section 4, Theorem 2 and its proof (p. 14).
