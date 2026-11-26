# Optimal pair matchings for sparse RNA structure alignment

**Setting.** RNAs $A$ and $B$ (average length $l$) carry fixed non-crossing secondary structures $P_A,P_B$ with on average $n$ base pairs. An alignment is a one-to-one relation $\mathcal A\subseteq P_A\times P_B$ preserving enclosure ($<_I$) and juxtaposition ($<_J$) between matched pairs; matched pairs cut both sequences into loop regions. Its score is

$$M=w_1\sum_{(p^A,p^B)\in\mathcal A}S_{str}(p^A,p^B)+w_2\sum S_{seq}(\mathcal L^A_{\mathcal A},\mathcal L^B_{\mathcal A}),$$

with base-pair substitution scores $S_{str}$, affine-gap sequence alignment scores $S_{seq}$ on corresponding loops, and no penalty for unmatched base pairs. Let $M[p^A,p^B]$ be the optimum for the regions enclosed by $p^A,p^B$ given that they are matched; the standard recursions over enclosed pairs and juxtaposed chains cost $O(n^4+n^2l^2)$.

**Triangle inequality (Observation 1).** For regions $A[i..j]$, $B[i'..j']$ and split points $i\le k<j$, $i'\le k'<j'$,

$$M[i,j;i',j']\ge M[i,k;i',k']+M[k+1,j;k'+1,j'].$$

**Lemma 1 (dominated matchings).** Let $p^\chi\,{<_I}\,p^A\,{<_I}\,p^*$ in $A$ (similarly in $B$), with pseudo pairs for the flanking regions. If

$$M[p^\beta_A,p^\beta_B]+M[p^\chi_A,p^\chi_B]+M[p^\delta_A,p^\delta_B]\ge M[p^A,p^B]$$

for some inner $p^\chi$, then for every enclosing $p^*$ the alignment avoiding the match $(p^A,p^B)$ scores at least as well as any using it. Matchings not dominated in this way are **optimal pair matchings (OPMs)**; in practice $(p^A,p^B)$ is kept iff $M[p^A,p^B]\ge M[\bar p^A,\bar p^B]$, where $\bar p$ are the pseudo pairs one position outside $p$.

**Sparse recursion.** Restricting the maximization in the multiloop/interior term and in the chain term to OPMs gives $M_l[p^A,p^B]=S_{str}(p^A,p^B)+\max_{o_{i,i'}\in\mathcal O}\{M_c[p_i^A,p_{i'}^B]+S_{seq}(L_r(p_i^A,p^A),L_r(p_{i'}^B,p^B))\}$, still exact, with running time

$$O\big(z\,(n^2+l^2)\big),\qquad z=|\mathcal O|,\ n<z\ll n^2 .$$

Under the polymer-zeta property one expects $z=O(n)$, and with $n=O(l)$ the expected time is cubic, $O(zl^2)$. A unit-time upper bound $\hat M_h$ on the hairpin term lets the $O(l^2)$ hairpin alignment be skipped whenever $M_l>\hat M_h$.

## Depends on

- [RNA secondary structure](../../nussinov-algorithm-for-rna-secondary-structure/is-structure.md)

## Expansion

Splitting a region and aligning the parts separately can only lose score, which is the triangle inequality. If an inner split already matches the score obtained by matching $p^A$ with $p^B$, then inside any larger enclosing context the split alignment, which is compatible with more matchings outside, dominates; so only non-dominated matchings need to be referenced by enclosing pairs. Each DP cell then scans $O(z)$ OPMs instead of $O(n^2)$ pairs, and loop alignments are needed only for loops bounded by OPMs. The expected sparsity $z=O(n)$ rests on the polymer-zeta assumption about RNA, not on a proof.

## Sources

- C. Zhong, S. Zhang, "Efficient alignment of RNA secondary structures using sparse dynamic programming", BMC Bioinformatics 14:269 (2013), Methods: Equation (1) and Equations (2)–(5) (original recursions), Observation 1 and Lemma 1 (section "Triangular inequality and optimal pair matchings"), section "Detection of optimal pair matchings", Equations (6)–(10) (section "A new algorithm with cubic time complexity"), <https://doi.org/10.1186/1471-2105-14-269>, PMCID: PMC3871798.
