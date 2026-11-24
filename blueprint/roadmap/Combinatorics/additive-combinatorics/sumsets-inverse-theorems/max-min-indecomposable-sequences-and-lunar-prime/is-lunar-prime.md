# Lunar primes

Let $b$ be a natural number. The lunar unit of base $b$ is the constant polynomial $b - 1$.
The predicate `IsLunarPrime` records the factorization condition: for all sequences
$g, h : \mathbb{N} \to \mathbb{N}$ with all terms less than $b$ and $g \otimes h = f$,
at least one factor is the lunar unit. The paper's Definition 5 additionally requires $f$ to be
a nonunit; this predicate does not include that exclusion.

## Sources

- Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Definition 5.
