# Li–Stephens recombination likelihood on variation graphs

**Setting.** A variation graph $G$ has nodes labelled by nucleotide sequences, with $5'$ and $3'$ sides and edges between sides; $S(G)$ is the set of finite paths through oriented nodes, each spelling a sequence $\mathrm{seq}(h)$. A reference cohort $H$ is a multiset of paths in $S(G)$. A *recombination mosaic* $x$ is a concatenation of subsequences of the $\mathrm{seq}(p)$, $p \in H$. Between consecutive bases a mosaic recombines to a given other haplotype with probability $\pi_r$ and stays on its current haplotype with probability $\pi_c = 1 - (|H| - 1)\pi_r$, so

$$P(x \mid G, H) = \pi_r^{R(x)}\, \pi_c^{|x| - R(x)},$$

where $|x|$ is the length in base pairs and $R(x)$ the number of recombinations. For a path $h \in S(G)$ with mosaic set $\chi(h)$ (mosaics following the same node path),

$$P(h \mid G, H) = \sum_{x \in \chi(h)} P(x \mid G, H) = \pi_c^{|h|} \sum_{x \in \chi(h)} \rho^{R(x)}, \qquad \rho = \pi_r / \pi_c .$$

**Equivalence classes.** For node indices $a \le b$ of $h$, let $S^a_b$ be the set of subintervals of reference haplotypes that match $h$ from $a$ to $b$ and cannot be extended to the node before $a$ (left-maximal). For any two $s_1, s_2 \in S^a_b$ there is a recombination-count-preserving bijection between the mosaics of the prefix $h_b$ whose last segment comes from $s_1$ and those whose last segment comes from $s_2$. Hence $R_b(a) = \sum_{x} \rho^{R(x)}$ over mosaics of $h_b$ ending in a given element of $S^a_b$ depends only on $a$, and with $A_b = \{a : S^a_b \ne \emptyset\}$,

$$P(h_b \mid G, H) = \pi_c^{|h_b|} \sum_{a \in A_b} |S^a_b|\, R_b(a).$$

**Theorem (complexity).** The values $R_b(\cdot)$ follow from $R_{b-1}(\cdot)$ by a linear recurrence using two shared sums over $A_{b-1}$; the class sizes satisfy $|S^a_b| = J^a_b - J^{a-1}_b$, where $J^a_b$ is the number of reference subpaths matching $h$ between nodes $a$ and $b$, each obtained from $J^a_{b-1}$ by one $O(1)$ extension of a graph positional Burrows–Wheeler search interval. Therefore $P(h \mid G, H)$ is computed in $O(n \cdot m)$ time, with $n = |h|$ and $m = \max_b |A_b| \le |H|$.

**Mutation.** With mutations independent of recombination, $P_{\mathrm{tot}}(h \mid G, H) = \sum_{h'} P_m(h \mid h')\, P_r(h' \mid G, H)$, where $P_m$ is supported on paths differing from $h$ by short non-overlapping substitutions, indels and cycles.

## Expansion

The mosaic formula is the Li–Stephens recombination process applied to every base: each inter-base step either switches to one of $|H| - 1$ other haplotypes or not. Summing over mosaics consistent with a node path factors out $\pi_c^{|h|}$, leaving a generating function in $\rho$ over recombination counts. Mosaics whose final segment lies in different but path-identical reference subintervals have identical histories up to relabelling of the source haplotype, which is the bijection; it collapses the state space from individual haplotypes to left-maximal match classes, typically far fewer than $|H|$, so runtime is empirically sublinear in cohort size. The recurrence weights $f_s(w, \ell) = (1 + (w-1)\rho)^{\ell - 1}$ and $f_t(\ell) = (1 - \rho)^{\ell - 1}$ account for the $\ell$ base pairs of node $b$ during which recombination among the $w$ matching subintervals can occur. Recombination rate and effective cohort size may vary along the graph without changing the complexity.

## Sources

- Y. Rosen, J. Eizenga, B. Paten, "Modelling haplotypes with respect to reference cohort variation graphs", Bioinformatics (2017), Section 2.2 (mosaic likelihood, Eqs. 1–3), Section 2.3 (Definitions 1–4, Claim 1, Corollary 1, Eqs. 4–8), Section 2.4 (Definition 5, Claim 2, gPBWT) and Section 2.5 (mutation model, Eq. 9). <https://doi.org/10.1093/bioinformatics/btx236> (PMC5870562).
