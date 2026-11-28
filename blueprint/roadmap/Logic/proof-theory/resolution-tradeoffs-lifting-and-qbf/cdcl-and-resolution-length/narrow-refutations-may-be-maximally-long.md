# Narrow resolution refutations may be maximally long

The counting bound $n^{O(w)}$ on resolution length in terms of width $w$ is tight: there are 3-CNF formulas refutable in width and space $O(w)$ whose every refutation, in resolution, PCR or Sherali-Adams, has size $n^{\Omega(w)}$.

**Theorem (main theorem).** Let $w = w(n)$ satisfy $w = O(n^c)$ for some constant $c < 1/2$. There are 3-CNF formulas $F_{n,w}$ with $O(w n)$ clauses over $O(n)$ variables such that $F_{n,w}$ has a resolution refutation in simultaneous size $n^{O(w)}$, width $O(w)$ and space $O(w)$, and any refutation of $F_{n,w}$ in resolution, polynomial calculus resolution (PCR) or Sherali-Adams has size $n^{\Omega(w)}$.

**Resolution version.** Let $k = k(n)$ be integer-valued with $2 \le k(n) \le n / (4 \log n)$, as the linked family requires $k \ge 2$ and $n \ge k$. The 3-CNF versions $F_{n,k}$ of the relativized pigeonhole formulas $\mathrm{RPHP}^k_{n,k-1}$, with $O(n^2)$ variables and $O(k n^2)$ clauses, have tree-like resolution refutations of size $O(k^k n^k)$, width $2k+1$ and space $2k+3$, while every resolution refutation of $F_{n,k}$ has size

$$
\Omega\Bigl(\frac{n^{k-1}}{(4k \log n)^k}\Bigr).
$$

For $k(n) = O(n^c)$ with $c < 1$ the upper bound is $n^{O(k)}$ and the lower bound is $n^{\Omega(k)}$.

**Corollary.** There are formulas over $n$ variables refutable in resolution width $w$ on which every resolution-based CDCL solver needs time $n^{\Omega(w)}$, unconditionally, since no such solver runs faster than the shortest resolution refutation. Atserias, Fichte and Thurley showed that on formulas of resolution width $w$ a CDCL solver with random decisions needs time $n^{O(w)}$ with high probability; this upper bound is therefore optimal up to constants in the exponent.

## Expansion

Upper bound: a tree-like refutation guesses the images of the $k$ pigeons one at a time and refutes the resulting pigeonhole instance on $k$ pigeons and $k-1$ holes, staying within width $2k+1$. Lower bound: a Furst-Saxe-Sipser style random restriction is applied to a hypothetical refutation of size $n^{o(k)}$. Noticeably wide clauses are very likely satisfied and vanish, while the remaining clauses are very likely shortened below width $k$; taking both cases into account lets the threshold for "wide" be large. The formula and restriction are designed so that the restricted formula is a bounded-width pigeonhole formula with $k$ pigeons and $k-1$ holes, so by counting some restriction yields a refutation of it in width less than $k$, which a separate argument rules out. For PCR and Sherali-Adams the restriction part is the same and the final step shows that the restricted refutations have impossibly low degree or rank.

## Depends on

- [Relativized pigeonhole principle formulas](relativized-pigeonhole-formulas.md)
- [Width of a derivation](../../../propositional-logic/resolution-size-and-width/derivation-width.md)
- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)
- [Tree-like resolution derivation](../../../propositional-logic/resolution-size-and-width/resolution-tree.md)
- [Variable space and total space of resolution refutations](../space-and-pebbling-tradeoffs/variable-and-total-space.md)
- [Conflict-driven clause learning as a proof system](cdcl-proof-system.md)

## Proof depends on

None.

## Sources

- A. Atserias, M. Lauria, J. Nordström, "Narrow proofs may be maximally long", *ACM Transactions on Computational Logic* 17(3), 2016 (conference version CCC 2014), doi:10.1145/2898435, arXiv:1409.2731v1 (main theorem and its CDCL corollary in Section 1.2; resolution version opening Section 3).
- J. Nordström, "On the interplay between proof complexity and SAT solving", *ACM SIGLOG News* 2(3), 2015, 19-44, doi:10.1145/2815493.2815497 (Section 2.2, stating the tightness of the counting bound).
