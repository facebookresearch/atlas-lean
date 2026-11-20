# Erdős's theorem on graphs of high girth and high chromatic number

For all natural numbers
$k$ and $g$ with $g \ge 3$, there is a finite simple graph $G$ that has a cycle, whose girth
(the length of a shortest cycle) is at least $g$, and whose chromatic number is at least $k$.

In particular, there are finite graphs of arbitrarily high girth and chromatic number.

## Background

- [First moment method](../../../Combinatorics/probabilistic-combinatorics/first-and-second-moment-methods/measure-real-one-le-le-integral.md): Erdős's proof takes $G(n, p)$ with $p = n^{\theta - 1}$, uses Markov's inequality to show that with high probability there are fewer than $n/2$ cycles of length at most $g$, and deletes a vertex from each (the alteration method; Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, Theorem 3.9 and its proof).

## Sources

- P. Erdős, Graph theory and probability, Canad. J. Math. 11 (1959), 34–38, DOI 10.4153/CJM-1959-003-9.
