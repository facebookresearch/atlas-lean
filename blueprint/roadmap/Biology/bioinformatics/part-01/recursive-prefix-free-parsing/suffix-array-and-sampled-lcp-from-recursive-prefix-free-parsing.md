# Suffix array and sampled LCP from recursive prefix-free parsing

**Setting.** Let $(D_T,P_T)$ be the prefix-free parse of a text $T$ with window $w_1$ and $(D_P,P_P)$ the prefix-free parse of $P_T$ with window $w_2$, with proper phrase suffixes $S_T$ and the hard-easy/hard-hard classification of [BWT from recursive prefix-free parsing](bwt-from-recursive-prefix-free-parsing.md). Every suffix $T[i..n]$ begins with exactly one proper phrase suffix $\alpha_i\in S_T$ (its *representative prefix*), so the suffix array splits into ranges $[b_1,e_1],\dots,[b_k,e_k]$ with representative prefixes $\alpha_1\prec\dots\prec\alpha_k$.

**Observation 1.** If $\alpha$ is a proper phrase suffix of a phrase $d\in D_T$ and the end positions $EP_d[1..]$ of all occurrences of $d$ in $T$ are known, the SA value of the $j$-th occurrence of $\alpha$ inside $d$ is $EP_d[j]-|\alpha|+1$.

**Lemma 3.** For every $\alpha\in S_T$ with occurrences $i_1,\dots,i_k$ in $T$, the lexicographic order of the suffixes $T[i_1..],\dots,T[i_k..]$ can be found in $O(|D_T|+|D_P|+|P_P|)$ workspace (treating every $\alpha$, including easy ones, as hard-easy or hard-hard).

**Theorem 2.** The suffix array of $T$ can be computed from $D_T$, $D_P$ and $P_P$ in $O(|D_T|+|D_P|+|P_P|)$ working space.

**Theorem 3.** The LCP array sampled at the first position of every BWT run can be computed in the same $O(|D_T|+|D_P|+|P_P|)$ working space.

## Depends on

- [BWT from recursive prefix-free parsing](bwt-from-recursive-prefix-free-parsing.md)

## Expansion

Single-level PFP gets SA values from Observation 1 but needs end positions for every occurrence of every $D_T$ phrase, i.e. $O(|P_T|)$ words. The recursive version stores end positions only for occurrences of second-level meta-phrases $d'\in D_P$; the text length of a meta-phrase is the sum of the lengths of its constituent $D_T$ phrases minus their overlaps, so the end position in $T$ of any $D_T$ phrase inside an occurrence of $d'$ is recovered by subtracting the lengths of the phrases that follow it. Easy suffixes need explicit treatment because, although their BWT characters are all equal, their SA values still depend on the order of occurrences; Lemma 3 supplies that order from the scan over $S_P$ and the grid of meta-phrase positions in $\mathrm{BWT}_{P_P}$. For a run head $i$ and its SA predecessor $j$, the LCP is computed hierarchically: compare the representative phrase suffixes $\alpha_i,\alpha_j$; if equal, compare the proper meta-phrase suffixes containing them (expanding each meta-character to its phrase length); if those are also equal, a range-minimum query on the LCP array of $P_P$ counts the matching meta-phrases that follow, and the first mismatching meta-phrase, meta-character and finally character give the value. These arrays underlie $r$-index style pangenome aligners.

## Sources

- Ferro E, Oliva M, Gagie T, Boucher C, "Building a pangenome alignment index via recursive prefix-free parsing" (2024), Observation 1, Lemma 3, Theorem 2 and Theorem 3 (Method details, "Computation of the SA" and "Computation of the LCP array"), <https://doi.org/10.1016/j.isci.2024.110933>, PMCID PMC11465122.
