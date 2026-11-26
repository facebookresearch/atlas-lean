# Counting RNA secondary structures by partial stacks and loop sizes

**Setting.** An RNA secondary structure on bases $1,\dots,n$ is a set of arcs $(i,j)$, $i<j$, each base in at most one arc, with $j-i\ge2$ (no empty hairpin) and no two arcs crossing (any two arcs are disjoint or nested). Arcs are base pairs and the remaining bases are *isolated*. A *partial stack* is a maximal set of mutually nested arcs whose left ends are consecutive; its length is the number of arcs. A *loop* is the set of isolated bases directly covered by the same arc (the outer region counts via an added arc $(0,n+1)$); its *size* is the number of elements, isolated bases or arcs, immediately covered by that arc.

Throughout, structures have $b+1$ base pairs and $k$ isolated bases.

**Theorem.**

1. (Schmitt–Waterman.) The number of such structures is the Narayana number

$$\frac{1}{b+k}\binom{b+k}{k}\binom{b+k}{k-1}.$$

2. The number with exactly $l$ partial stacks is $\binom{b+k-1}{k-1}$ for $l=1$ and, for $l>1$,

$$\frac{1}{l-1}\binom{l+b-1}{l-2}\binom{b+1}{l}\binom{b+k-1}{k-l}.$$

3. The number $H_h(b,k)$ in which every partial stack has length at most $h$ is

$$H_h(b,k)=\frac{1}{b+k}\binom{b+k}{k}\sum_{0\le i\le\frac{b+1}{h+1}}(-1)^i\binom{k}{i}\binom{b+k-i(h+1)}{k-1},$$

and $H_{b+1}(b,k)$ is the Narayana number of part 1.

4. The number $L_l(b,k)$ in which every loop has size at most $l$ is

$$L_l(b,k)=\frac{1}{b+1}\binom{b+k}{b}\sum_{0\le i\le\frac{k-1}{l}}(-1)^i\binom{b+1}{i}\binom{b+k-1-il}{k-1-il}.$$

Summing part 2 over $l$ gives the identity $\frac{1}{b+k}\binom{b+k}{k}\binom{b+k}{k-1}=\binom{b+k-1}{k-1}+\sum_{l>1}\frac{1}{l-1}\binom{l+b-1}{l-2}\binom{b+1}{l}\binom{b+k-1}{k-l}$.

## Expansion

Chen's bijection maps a structure with $k$ isolated bases to a plane tree with $b+k$ edges in which isolated bases and arcs alternate along levels: the first isolated base is the root, arcs covering an isolated base become its children from outermost to innermost, and each later isolated base hangs from its innermost covering arc. Under this map partial stacks become runs of children of one even-level vertex and loops become children of one odd-level vertex, so length and size constraints become bounds on vertex degrees by parity. Counting plane trees with prescribed degree bounds is done by Lagrange inversion, and the alternating sums are inclusion–exclusion over vertices that violate the bound. The original Schmitt–Waterman bijection, which maps arcs and isolated bases to tree vertices, gives the Narayana count by number of leaves.

## Sources

- Ricky X. F. Chen, Christian M. Reidys, Michael S. Waterman, "Exact enumeration of RNA secondary structures by helices and loops", arXiv:2407.06220 (2024): Section 2 (definitions, the Schmitt–Waterman bijection and Chen's bijection to plane trees, partial stacks, helices and loops), Section 3.1 (theorems on partial stacks, maximum partial stack length, maximum loop size and joint constraints; the Narayana corollary and the summation identity). <https://doi.org/10.48550/arXiv.2407.06220>
