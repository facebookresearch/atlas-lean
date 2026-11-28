# Edge counts on the weight levels of the cumomer cascade

**Cumomers.** In a metabolite pool whose backbone has $s$ labelable atom positions, an isotopomer assigns each position the state labeled or unlabeled ($2^s$ isotopomers). A cumomer assigns each position the state labeled or wildcard, and stands for the set of isotopomers agreeing on its labeled positions; its *weight* is the number of labeled positions (Definition 1). Applying the translation rules of Definition 2 to an isotopomer network (replace unlabeled positions by wildcards; send weight-violating splitting transitions to a sink; remove weight-0 cumomers) gives the cumomer network. Its remaining transitions conserve or increase weight, so the network is a *cascade* of weight levels $k=1,2,\dots$, and on each level the labeling balance equations are linear in that level's unknowns. Level 1 is the atom transition network.

**Width (Definition 4).** A unimolecular reaction $A\to B$ moving all $s$ positions has width $s$; a bimolecular reaction $A+B\rightleftharpoons C$ with $q+r=s$ positions has widths $q$ (between $A$ and $C$) and $r$ (between $B$ and $C$). A reaction sequence through pools $P_0,\dots,P_\ell$ has the width of the largest fragment it transports end to end.

**Lemma 2 (edges per level).** On weight level $k$ of the cascade,

- a unimolecular reaction $A\to B$ of width $s$ induces $\binom{s}{k}$ edges;
- a bimolecular assembly $A+B\to C$, or splitting $C\to A+B$, with widths $q$ and $r$ induces $\binom{q}{k}+\binom{r}{k}$ edges; a reversible reaction induces this many in each direction.

A pool with $s$ labelable positions contributes $\binom{s}{k}$ cumomer nodes to level $k$. Since $\binom{q}{k}+\binom{r}{k}\le\binom{q+r}{k}$ (Vandermonde's convolution), on every level an assembly product $C$ has at least as many cumomers as there are weight-conserving transitions into it from $A$ and $B$; the remaining cumomers of $C$ are fed only by assembly transitions from lower levels.

## Expansion

A weight-$k$ cumomer of the product is determined by which $k$ of the transported positions are labeled, and a reaction transporting a fragment of $s$ positions maps each $k$-subset of the fragment to one $k$-subset in the product. Counting $k$-subsets gives $\binom{s}{k}$; for a bimolecular reaction the two substrates contribute independently. The node count follows in the same way. The source uses these counts to argue that the higher levels are less connected (its Lemma 1); the counting above is the part that holds without further assumptions.

## Sources

- M. Weitzel, W. Wiechert, K. Nöh, "The topology of metabolic isotope labeling networks", BMC Bioinformatics 8 (2007) 315. <https://doi.org/10.1186/1471-2105-8-315>, PMCID PMC2233644. Definitions 1, 2 and 4, Lemma 2 and the appendix proof of Lemma 1.
