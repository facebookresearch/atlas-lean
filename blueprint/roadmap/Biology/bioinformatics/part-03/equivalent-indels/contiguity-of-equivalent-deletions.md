# Contiguity of equivalent deletions

**Setting.** Let $r = r_1 r_2 \cdots r_N$ be a reference sequence and, for $1 \le j \le N - \ell + 1$, let $D_j$ be the deletion of the length-$\ell$ block $r_j \cdots r_{j+\ell-1}$, producing $r^{(j)} = r_1 \cdots r_{j-1}\, r_{j+\ell} \cdots r_N$. Two deletions $D_i, D_j$ of the same length are **equivalent** if $r^{(i)} = r^{(j)}$, i.e. they produce the same alternative sequence although their positions and deleted alleles differ.

**Theorem.**
1. (Neighbours.) $D_j$ and $D_{j+1}$ are equivalent if and only if $r_j = r_{j+\ell}$, i.e. the first deleted nucleotide equals the nucleotide immediately after the deleted block.
2. (Overlapping deletions.) If $D_i$ and $D_j$ with $i < j < i + \ell$ are equivalent, then every $D_k$ with $i \le k \le j$ is equivalent to them.
3. (Distant deletions.) If $D_i$ and $D_j$ with $j \ge i + \ell$ are equivalent, then again every $D_k$ with $i \le k \le j$ is equivalent to them.

Consequently each equivalence class of length-$\ell$ deletions is a contiguous run of start positions $\{a, a+1, \dots, b\}$, found by extending from any member while $r_k = r_{k+\ell}$ holds; the deleted alleles in one class are cyclic rotations of one another, and the stretch $r_a \cdots r_{b+\ell-1}$ has period $\ell$, since $r_k = r_{k+\ell}$ for $a \le k < b$. The same holds for insertions by exchanging the roles of reference and alternative sequence.

## Expansion

Shifting a deletion one base to the right removes $r_{j+\ell}$ instead of $r_j$ and keeps everything else, so the two products agree exactly when those two bases match, which is part 1. For two equivalent deletions, comparing the products letter by letter forces the stretch between them to be built from repeated copies of the deleted block, and part 1 then applies at every intermediate shift, which gives parts 2 and 3 and the transitivity needed for contiguity. Choosing one canonical representative per class (for instance the leftmost start) removes duplicate database entries that a fixed distance window would either miss or wrongly merge, and shows that the precise position of an indel inside a repeat is not identifiable from sequence alone.

## Sources

- J. Assmus, J. Kleffe, A. O. Schmitt, G. A. Brockmann, "Equivalent indels — ambiguous functional classes and redundancy in databases", PLoS ONE 8(5): e62803 (2013), Theorems 1–3, <https://doi.org/10.1371/journal.pone.0062803>, PMCID PMC3642179.
