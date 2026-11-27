# Generating permutations and bases for bounded block transposition distance

A **block transposition** of $\pi = \pi_1\cdots\pi_n$ exchanges two adjacent factors: $\alpha\,\beta\,\gamma\,\delta \mapsto \alpha\,\gamma\,\beta\,\delta$. A **prefix block transposition** is one with $\alpha$ empty. Write $d_{td}(\pi)$ and $d_{ptd}(\pi)$ for the least number of such moves turning $\pi$ into the identity, and

$$B_k^{(td)} = \{\pi : d_{td}(\pi) \le k\}, \qquad B_k^{(ptd)} = \{\pi : d_{ptd}(\pi) \le k\}.$$

These sets are permutation classes (closed under taking patterns). A permutation is **plus irreducible** if $\pi_{i+1} \ne \pi_i + 1$ for all $i$, i.e. all its strips (maximal runs of consecutive increasing values in consecutive positions) have length one. $MI(\pi)$ denotes the set of **monotone inflations** of $\pi$ (replace each entry by a monotone run), and $\pi$ is **generating** for $B_k$ if it is a maximal plus irreducible permutation of $B_k$ in the pattern order. Then $B_k$ is the union of $MI(\pi)$ over its generating permutations.

**Theorem (block transpositions).** For every $k \ge 1$:

1. the generating permutations of $B_k^{(td)}$ are exactly the plus irreducible permutations of length $3k+1$ at block transposition distance $k$ from the identity;
2. every basis element of $B_k^{(td)}$ has length at most $3k+1$;
3. the basis of $B_1^{(td)}$ is $\{321, 2143, 2413, 3142\}$.

**Theorem (prefix block transpositions).** For every $k \ge 1$:

1. the generating permutations of $B_k^{(ptd)}$ are exactly the plus irreducible permutations of length $2k+1$ at prefix block transposition distance $k$, and there are $(2k)!/2^k$ of them;
2. every basis element of $B_k^{(ptd)}$ has length at most $2k+1$;
3. the basis of $B_1^{(ptd)}$ is $\{132, 321\}$, and the basis of $B_2^{(ptd)}$ consists of $1432, 2143, 4321$ together with fifteen permutations of length $5$.

## Expansion

A single block transposition is determined by three cut positions, so a monotone inflation of a plus irreducible permutation followed by one more move is again a monotone inflation of a permutation obtained by choosing a multiset of three cut positions; iterating from the identity shows that $k$ moves produce plus irreducible permutations of length at most $3k+1$, and the maximal ones are exactly those of that length at distance $k$. For prefix moves the first cut is fixed at the start, leaving two free cuts and length $2k+1$. A basis element is a minimal permutation outside the class, so deleting any entry yields a member of $B_k$; comparing with the generators bounds its length by the generator length.

## Sources

- Giulio Cerbai, Luca Ferrari, "Permutation patterns in genome rearrangement problems: The reversal model", Discrete Applied Mathematics 279 (2020), 34–48, <https://doi.org/10.1016/j.dam.2019.10.012>. Published version of arXiv:1808.02653, cited next; locators there refer to the arXiv version.
- Giulio Cerbai, Luca Ferrari, "Permutation patterns in genome rearrangement problems", arXiv (2018). Proposition 2.1, Proposition 2.3, Theorems 2.4–2.5, Proposition 2.6, Theorems 3.2–3.4, Proposition 3.5. <https://doi.org/10.48550/arXiv.1808.02653>
