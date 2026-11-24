# Ceiling parity count from the floor parity count

For a natural number $m$, let
$\mathcal{C}_m$ and $\mathcal{F}_m$ be the numbers of integers $k$ with $1 \le k \le m$ for which
$\lceil m/k \rceil$, respectively $\lfloor m/k \rfloor$, is odd. Then for every natural number
$n$, $\mathcal{C}_{n+1} = (n + 1) - \mathcal{F}_n$.

The source prints a second equality $\mathcal{C}_n = \sum_{d=2}^{n} \lfloor n/d \rfloor (-1)^d$,
which is not part of this statement: it fails at $n = 3$, where $\mathcal{C}_3 = 2$ but the sum
is $1 - 1 = 0$.

## Sources

- Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024), Article 24.2.5, Proposition 9 (`jis-2024-24.2.5-prop-9`).
