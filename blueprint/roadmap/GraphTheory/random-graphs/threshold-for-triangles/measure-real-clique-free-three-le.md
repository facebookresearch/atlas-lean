# Second moment bound for triangles in G(n, p)

For $0 < p \le 1$ and $n \ge 3$,

$$\Pr[G(n, p) \text{ is triangle-free}] \le \frac{1 + 3 n p^2}{\binom n3 p^3} .$$

Let $A_T$ be the event that the triple $T$ spans a triangle and $\mu = \binom n3 p^3$ the expected number of triangles. Triangles without a common edge are independent, so the [dependency graph](share-edge.md) joins triples sharing a pair. A dependent pair spans [at least five edges](five-le-card-union.md), so $\Pr[A_T \cap A_{T'}] \le p^5$, and each triple has [at most $3n$ dependent partners](card-share-edge-le.md); hence $\Delta \le 3 n p^2 \mu$. The [second moment method for counts of events](../../../Combinatorics/probabilistic-combinatorics/first-and-second-moment-methods/measure-real-forall-not-mem-le.md) gives $\Pr[\text{no } A_T] \le (\mu + \Delta)/\mu^2 \le (1 + 3np^2)/\mu$.

## Informally uses

- [Second moment method for counts of events](../../../Combinatorics/probabilistic-combinatorics/first-and-second-moment-methods/measure-real-forall-not-mem-le.md): the bound $(\mu + \Delta)/\mu^2$.
- [Two triangles sharing an edge span five edges](five-le-card-union.md): the bound $p^5$ on dependent pairs.
- [A triangle shares an edge with at most 3n others](card-share-edge-le.md): the count of dependent pairs.

## Sources

- Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, proof of Proposition 4.11, using Lemma 4.8 and Corollary 4.13 (the notes compute $\operatorname{var} X \lesssim n^3p^3 + n^4p^5$).
