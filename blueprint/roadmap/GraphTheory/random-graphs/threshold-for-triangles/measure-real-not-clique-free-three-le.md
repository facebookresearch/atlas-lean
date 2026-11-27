# First moment bound for triangles in G(n, p)

For every $p \in [0, 1]$,

$$\Pr[G(n, p) \text{ contains a triangle}] \le \binom n3 p^3,$$

the expected number of triangles: each of the $\binom n3$ vertex triples spans a triangle with probability $p^3$, and the union bound adds these up.

## Informally uses

- [First moment method](../../../Combinatorics/probabilistic-combinatorics/first-and-second-moment-methods/measure-real-one-le-le-integral.md): $\Pr[X \ge 1] \le \mathbb E X$ for the number $X$ of triangles, here in union-bound form.
- [Probability that a random subset contains a given set](../../../Combinatorics/probabilistic-combinatorics/janson-s-inequalities/random-subset-law-real-contains-event.md): a triple spans a triangle with probability $p^3$.

## Sources

- Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, proof of Proposition 4.11.
