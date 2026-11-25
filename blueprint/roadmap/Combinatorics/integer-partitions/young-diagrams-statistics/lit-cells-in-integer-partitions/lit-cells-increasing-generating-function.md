# Generating function for lit cells of weakly increasing bargraphs

Let
$P(q) = \sum_{n \ge 0} p(n) q^n$ be the partition generating function, and let
$L(q) \in \mathbb{Z}[[q]]$ be the power series whose coefficient of $q^n$ is the total number of
lit cells over all partitions of $n$ drawn as weakly increasing bargraphs. Then

$$L(q) = 2P(q) \sum_{i \ge 1} \frac{q^i}{1 - q^i} - P(q) \frac{q}{1 - q}$$

and

$$L(q) = P(q) \sum_{i \ge 1} \frac{q^i (1 + q^i)}{1 - q^i},$$

where the sums converge coefficientwise.

## Sources

- Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer Partitions*, INTEGERS 24 (2024), Article A56, Proposition 1, eq. (5).
