# Generating function for lit nodes of weakly increasing diagrams

Let
$P(q) = \sum_{n \ge 0} p(n) q^n$ be the partition generating function, and let
$N(q) \in \mathbb{Z}[[q]]$ be the power series whose coefficient of $q^n$ is the total number of
lit nodes over all partitions of $n$ drawn as weakly increasing Ferrers diagrams of nodes. Then

$$N(q) = 1 + P(q) \Bigl(\sum_{i \ge 1} \frac{2q^i}{1 - q^i} - 1\Bigr),$$

where the sum converges coefficientwise.

## Sources

- Aubrey Blecher, Arnold Knopfmacher, and Michael Mays, *Casting Light on Integer Partitions*, INTEGERS 24 (2024), Article A56, Proposition 2, eq. (7).
