# Strings with the same q-gram composition are related by transpositions and rotations

Two strings have the same $q$-gram composition (the same shingles) if every string of length $q$ occurs in them the same number of times. For $(q-1)$-grams $z_1, z_2$ and arbitrary strings $x_i$, a transposition maps $x_1 z_1 x_2 z_2 x_3 z_1 x_4 z_2 x_5$ to $x_1 z_1 x_4 z_2 x_3 z_1 x_2 z_2 x_5$, and a rotation maps $z_1 x_1 z_2 x_2 z_1$ to $z_2 x_2 z_1 x_1 z_2$; both preserve the $q$-gram composition. Kontorovich and Trachtenberg (2012, Section III.A) record that Ukkonen conjectured, and Pevzner proved, that two strings with the same $q$-gram composition are related through these two transformations. In the graph-theoretic framework they attribute to Pevzner, the shingles are the edges, with multiplicities, of a de Bruijn-type multigraph on $(q-1)$-grams, an edge joining the prefix and the suffix of its shingle, and the strings consistent with a multiset of shingles correspond to Eulerian trails of this multigraph; the result yields a simple test of whether a string is uniquely decodable from its shingles, with naive worst-case running time $\Theta(n^4)$ for strings of length $n$.

## Depends on

- [Every Eulerian trail spells a string with the same k-mer multiset](../../../Biology/bioinformatics/de-bruijn-graph-genome-assembly/kmers-spell-perm.md)
- [The (k-1)-mer walk of a string is an Eulerian trail](../../../Biology/bioinformatics/de-bruijn-graph-genome-assembly/zip-tail-kmers-perm.md)

## Expansion

1. The two transformations and the check that each preserves the $q$-gram composition.
2. The two transformations as reorderings of an Eulerian trail between repeated vertices of the multigraph.
3. Connectivity of the set of Eulerian trails of a fixed multigraph under these reorderings (Pevzner's argument via alternating Eulerian cycles).
4. The resulting unique-decodability test, and the linear-time streaming test of Kontorovich and Trachtenberg for two-character shingles, as a separate statement.

## Sources

- A. Kontorovich and A. Trachtenberg, Efficiently decoding strings from their shingles, arXiv:1204.3293 (2012), Sections I.A, II and III.A. <https://arxiv.org/abs/1204.3293>
- Original result: P. A. Pevzner, DNA physical mapping and alternating Eulerian cycles in colored graphs, Algorithmica 13 (1995), 77–105. <https://doi.org/10.1007/BF01188582> The theorem follows Kontorovich and Trachtenberg, Section III.A.
- Original result: E. Ukkonen, Approximate string-matching with q-grams and maximal matches, Theoret. Comput. Sci. 92 (1992), 191–211. <https://doi.org/10.1016/0304-3975(92)90143-4> The conjecture follows Kontorovich and Trachtenberg, Section III.A.
