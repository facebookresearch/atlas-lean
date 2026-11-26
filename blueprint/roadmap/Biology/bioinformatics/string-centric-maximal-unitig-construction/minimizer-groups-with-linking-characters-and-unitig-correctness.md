# Minimizer groups with linking characters and unitig correctness

**Read splitting.** Fix $m \le k$ and a hash $\mathrm{hash} : \Sigma^m \to \mathbb{Z}$; the minimizer of a string $x$ is $\mathrm{mini}(x) = \min\{\mathrm{hash}(y) : y \in \Sigma^m, \ y \text{ a substring of } x\}$. Each read is split into maximal substrings $S_1, \dots, S_\ell$, consecutive ones overlapping on $k-2$ characters, such that all $(k-1)$-mers of $S_i$ have the same minimizer $h$. Each $S_i$ is extended by its **linking characters**, the read characters immediately before and after it (or a sentinel), giving $S_i' = a \cdot S_i \cdot b$; consecutive extended pieces overlap on exactly $k$ characters. $S_i'$ is placed in the group $G_h$.

**Lemma 1.** Let $x$ be a $k$-mer occurring in the reads $R$ and in a group $G_h$. Then:

(a) $x$ occurs in at most one other group, and it occurs in two distinct groups if and only if $\mathrm{mini}(\mathrm{pre}_{k-1}(x)) \ne \mathrm{mini}(\mathrm{suf}_{k-1}(x))$;

(b) $\mathrm{occ}(x, G_h) = \mathrm{occ}(x, R)$;

(c) if $\mathrm{mini}(x) = h$ (so $x$ contains no linking character) and $x$ has a $(k-1)$ suffix-prefix overlap with a $k$-mer $y$ occurring in $R$ (in either order), then $y$ also occurs in $G_h$.

**Theorem 1.** Building unitigs inside each group by extending a $k$-mer $z$ to the right (or left) only when exactly one $k$-mer leaves $\mathrm{suf}_{k-1}(z)$ and exactly one enters the next $(k-1)$-mer, stopping at $k$-mers that contain a linking character, and then joining the partial unitigs that share such a boundary $k$-mer, outputs exactly the maximal unitigs of $R$ (Definition 1 without reverse complements). Replacing hashes by canonical hashes and tracking orientations during joining yields the canonical maximal unitigs.

**Randomized joining.** Partial unitigs to be joined form chains of pairs. In each round every chain is sent to the bucket of one of its unsealed ends chosen at random (with a placeholder in the bucket of the other end); chains meeting in a bucket are merged, and an end that finds neither a partner nor a placeholder is sealed. Two chains that must be merged land in the same bucket with probability at least $1/4$ per round, so the expected number of rounds until a given merge happens is at most $4$, while correctness does not depend on the random choices.

## Depends on

- [Canonical maximal unitigs as a spectrum-preserving string set](canonical-maximal-unitigs-as-a-spectrum-preserving-string-set.md)

## Expansion

A $k$-mer $x$ consists of two $(k-1)$-mers, and pieces are cut exactly where the window minimizer changes, so $x$ lands in the group of $\mathrm{pre}_{k-1}(x)$ and in that of $\mathrm{suf}_{k-1}(x)$ and nowhere else; this gives (a), and it also shows that every occurrence of $x$ is copied into $G_h$, which gives (b) and makes abundance filtering local. For (c), a neighbour $y$ sharing the minimizer $h$ lies in the same piece family, while a neighbour with a different minimizer is exactly a $k$-mer carrying a linking character, which was copied into $G_h$ by construction. Hence every branching test for a $k$-mer without linking characters can be answered inside its group, and the only global work is gluing the at most two partial unitigs that meet at each boundary $k$-mer.

## Sources

- A. Cracco, A. I. Tomescu, "Extremely fast construction and querying of compacted and colored de Bruijn graphs with GGCAT", Genome Research 33(7) (2023) 1198-1207, Methods (Definition 1, Lemma 1, Theorem 1, unitig merging), <https://doi.org/10.1101/gr.277615.122> (PMC10538363).
