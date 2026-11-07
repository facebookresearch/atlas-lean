# Bipartitions into distinct parts

Let $\operatorname{pd}(m)$ be the number of partitions
of $m$ into distinct parts. For a natural number $n$, $q(n)$ is the number of ordered pairs of
partitions into distinct parts whose sizes add up to $n$, that is,
$q(n) = \sum_{k=0}^{n} \operatorname{pd}(k) \operatorname{pd}(n-k)$.

Its generating function is $\sum_{n \ge 0} q(n) x^n = (-x; x)_\infty^2$, where
$(a; x)_\infty = \prod_{i \ge 0} (1 - a x^i)$.

## Sources

- Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd Parts*, INTEGERS 26 (2026), Article A60, Section 3 (definition of `q(n)` before Theorem 12).
