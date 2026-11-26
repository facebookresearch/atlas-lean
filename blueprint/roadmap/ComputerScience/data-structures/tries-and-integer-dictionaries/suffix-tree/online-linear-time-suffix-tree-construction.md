# Ukkonen's online linear-time suffix tree construction

For a string $T = t_1\cdots t_n$, the suffix trie represents all suffixes of $T$ and can have size quadratic in $n$; the suffix tree $\mathrm{STree}(T)$ represents it in linear space by keeping only branching states and leaves and labelling transitions by pairs of pointers into $T$ (at most $|T| - 1$ branching states and $2|T| - 2$ transitions). Ukkonen (1995, Theorem 2) proves that his Algorithm 2 constructs $\mathrm{STree}(T)$ online in time $O(n)$: after reading $t_1\cdots t_i$ it holds the suffix tree of that prefix, and to construct it the algorithm only needs access to the first $i$ symbols. The proof bounds the total time of the canonize procedure by $O(n)$ and the number of visited states by $2n$, through the depths of the successive active points; the constant time per visited state requires that the alphabet size be bounded independently of $n$. The algorithm uses suffix links on branching states, open transitions to leaves that grow automatically as symbols are appended, and the active and end points of each phase (Lemma 2); the final tree is obtained by appending an end marker not occurring elsewhere in $T$.

## Depends on

- [Suffix tree](../../../../ComputerScience/data-structures/tries-and-integer-dictionaries/suffix-tree/suffix-tree.md)

## Expansion

1. Suffix tries, their construction in time proportional to their size (Theorem 1), and suffix trees as their compacted form with reference pairs and suffix links.
2. The update from $\mathrm{STree}(T^{i-1})$ to $\mathrm{STree}(T^i)$: the boundary path, the active point and the end point (Lemma 2).
3. Open transitions and the procedures update and canonize.
4. The amortized analysis of Theorem 2, under a bounded alphabet, and the end marker.
5. The relation with suffix automata (DAWGs), as a separate statement.

## Sources

- E. Ukkonen, On-line construction of suffix trees, Algorithmica 14 (1995), 249–260, Sections 2–4, Lemma 2, Theorems 1 and 2. <https://doi.org/10.1007/BF01206331>
