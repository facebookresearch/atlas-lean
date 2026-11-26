# Isomorphic path copies in the cumomer cascade

**Cumomers.** In a metabolite pool whose backbone has $s$ labelable atom positions, an isotopomer assigns each position the state labeled or unlabeled ($2^s$ isotopomers). A cumomer assigns each position the state labeled or wildcard, and stands for the set of isotopomers agreeing on its labeled positions; its *weight* is the number of labeled positions (Definition 1). Applying the translation rules of Definition 2 to an isotopomer network (replace unlabeled positions by wildcards; send weight-violating splitting transitions to a sink; remove weight-0 cumomers) gives the cumomer network. Its remaining transitions conserve or increase weight, so the network is a *cascade* of weight levels $k=1,2,\dots$, and on each level the labeling balance equations are linear in that level's unknowns. Level 1 is the atom transition network.

**Width (Definition 4).** A unimolecular reaction $A\to B$ moving all $s$ positions has width $s$; a bimolecular reaction $A+B\rightleftharpoons C$ with $q+r=s$ positions has widths $q$ (between $A$ and $C$) and $r$ (between $B$ and $C$). A reaction sequence through pools $P_0,\dots,P_\ell$ has the width of the largest fragment it transports end to end.

**Lemma 3 (isomorphic paths).** Let reactions $R_1,\dots,R_\ell$ transport a (not necessarily contiguous) fragment through pools $P_0,\dots,P_\ell$, with $\mathrm{width}(R_1,\dots,R_\ell,P_0,\dots,P_\ell)=s$. Then the sequence induces, on each level $k=1,\dots,s$ of the cumomer cascade, $\binom{s}{k}$ pairwise node-disjoint directed paths isomorphic to the original reaction path, $2^s-1$ in total, and no isomorphic copy on levels above $s$.

Consequently cycles of reactions that retain a fragment of $s$ positions reappear as isomorphic copies of the same strongly connected component (Definition 6) on several levels, so the blocks of the level-wise linear cumomer balance systems are structurally repetitive; the source illustrates this on a central-metabolism network of *E. coli*.

## Depends on

- [Edge counts on the weight levels of the cumomer cascade](edge-counts-on-the-weight-levels-of-the-cumomer-cascade.md)

## Expansion

Every $k$-subset of the $s$ transported positions defines a cumomer in $P_0$ whose labeled atoms are carried along the whole sequence; following it step by step gives a copy of the reaction path on level $k$, and different subsets give disjoint cumomer nodes. Summing $\binom{s}{k}$ over $k$ gives $2^s-1$. Above level $s$ a copy would need more than $s$ labeled positions to survive every step, but some step of the sequence then splits off a labeled atom, and the translation rules route such weight-violating transitions to the sink.

## Sources

- M. Weitzel, W. Wiechert, K. Nöh, "The topology of metabolic isotope labeling networks", BMC Bioinformatics 8 (2007) 315. <https://doi.org/10.1186/1471-2105-8-315>, PMCID PMC2233644. Definitions 5–7, Lemma 3 and its appendix proof.
