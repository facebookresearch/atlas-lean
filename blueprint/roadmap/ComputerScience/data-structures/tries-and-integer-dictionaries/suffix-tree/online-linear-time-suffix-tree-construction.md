# Ukkonen's online linear-time suffix tree construction

For a string $T = t_1\cdots t_n$, the suffix trie represents all suffixes of $T$ and can have size quadratic in $n$; Ukkonen's suffix tree $\mathrm{STree}(T)$ represents it in linear space by keeping only branching states and leaves and labelling transitions by pairs of pointers into $T$. This tree is unmarked: it has no explicit final states, so a suffix that is a prefix of another suffix ends inside a transition or at a branching state rather than at a leaf. For this unmarked tree Section 3 gives linear space for every length and, for $|T| > 1$, at most $|T| - 1$ branching states and at most $2|T| - 2$ transitions between explicit states, the auxiliary state excluded. Ukkonen (1995, Theorem 2) proves that his Algorithm 2 constructs $\mathrm{STree}(T)$ online in time $O(n)$: after the phase that reads $t_i$ it holds Ukkonen's unmarked tree $\mathrm{STree}(t_1\cdots t_i)$ of the scanned prefix, to which the counts above apply, and to construct it the algorithm only needs access to the first $i$ symbols. The proof bounds the total time of the canonize procedure by $O(n)$ and the number of visited states by $2n$, through the depths of the successive active points; the constant time per visited state requires that the alphabet size be bounded independently of $n$. The algorithm uses suffix links on branching states, open transitions to leaves that grow automatically as symbols are appended, and the active and end points of each phase (Lemma 2); the input end marker is tested before the tree is updated, so it is not inserted. Processing instead a fresh end marker $\#$, not occurring in $T$, as one additional symbol constructs Ukkonen's tree $\mathrm{STree}(T\#)$ of the terminated string, in which every nonempty suffix of $T\#$, that is, each suffix of $T$ followed by $\#$, ends at a leaf, while the empty suffix ends at the root (Section 2). This tree represents the same terminated suffixes as the tree of the linked suffix tree page, which inserts them by starting index $0, \dots, |T|$ into a radix trie with start-index values; constructing that radix trie with the same representation is a separate step, and the linear-space argument of Section 3 relies on Ukkonen's representation, with transitions labelled by pairs of pointers into the string. The counts of $\mathrm{STree}(T\#)$ are the bounds above for the $|T| + 1$ symbols of $T\#$ (for $T = ab$ the root has the three transitions $ab\#$, $b\#$ and $\#$, more than $2|T| - 2 = 2$). Both versions use linear space.

## Depends on

- [Suffix tree](../../../../ComputerScience/data-structures/tries-and-integer-dictionaries/suffix-tree/suffix-tree.md): the terminated suffixes, represented by the tree obtained by processing one additional end-marker symbol.

## Expansion

1. Suffix tries, their construction in time proportional to their size (Theorem 1), and suffix trees as their compacted form with reference pairs and suffix links.
2. The update from $\mathrm{STree}(T^{i-1})$ to $\mathrm{STree}(T^i)$: the boundary path, the active point and the end point (Lemma 2).
3. Open transitions and the procedures update and canonize.
4. The amortized analysis of Theorem 2, under a bounded alphabet; the unmarked tree held after each phase, and the terminated tree obtained by processing a fresh end marker as one additional symbol, in which every nonempty suffix of $T\#$ ends at a leaf, with its bounds counted on $|T| + 1$ symbols.
5. The relation with suffix automata (DAWGs), as a separate statement.
6. Separate target: construction of the linked start-index-valued radix trie from Ukkonen's pointer-pair representation of the terminated tree.

## Sources

- E. Ukkonen, On-line construction of suffix trees, Algorithmica 14 (1995), 249–260, Sections 2–4, Lemma 2, Theorems 1 and 2. <https://doi.org/10.1007/BF01206331>
