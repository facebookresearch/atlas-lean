# Erdős's lower bound for diagonal Ramsey numbers (existence form)

Let $n, k$ be natural numbers with

$$\binom nk \, 2^{1 - \binom k2} < 1 .$$

Then there is a simple graph $G$ on $n$ vertices such that neither $G$ nor its complement contains $K_k$; equivalently, the edges of $K_n$ can be coloured red and blue with no monochromatic $K_k$.

Proof (first moment method): colour each edge red or blue independently with probability $1/2$, that is, take the [random subset of pairs](pair-graph.md) with $p = 1/2$. A fixed $k$-set $R$ is a red clique with probability $2^{-\binom k2}$ ([containment probability](../../../Combinatorics/probabilistic-combinatorics/janson-s-inequalities/random-subset-law-real-contains-event.md)) and a blue clique with the same probability ([avoidance probability](../../../Combinatorics/probabilistic-combinatorics/janson-s-inequalities/random-subset-law-real-avoid-event.md)). By the union bound over the $\binom nk$ sets, some $K_k$ is monochromatic with probability at most $\binom nk 2^{1-\binom k2} < 1$, so some colouring has none.

## Informally uses

- [Probability that a random subset contains a given set](../../../Combinatorics/probabilistic-combinatorics/janson-s-inequalities/random-subset-law-real-contains-event.md): the probability that a $k$-set is a red clique.
- [Probability that a random subset avoids a given set](../../../Combinatorics/probabilistic-combinatorics/janson-s-inequalities/random-subset-law-real-avoid-event.md): the probability that it is a blue clique.

## Background

- [First moment method](../../../Combinatorics/probabilistic-combinatorics/first-and-second-moment-methods/measure-real-one-le-le-integral.md): the union bound used here is the first moment bound $\Pr[X \ge 1] \le \mathbb E X$ for the number $X$ of monochromatic $K_k$.

## Sources

- Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, Theorem 1.4.
- P. Erdős, "Some remarks on the theory of graphs", *Bull. Amer. Math. Soc.* 53 (1947).
