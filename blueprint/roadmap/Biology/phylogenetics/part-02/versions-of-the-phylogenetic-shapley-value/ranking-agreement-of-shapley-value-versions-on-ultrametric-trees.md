# Rankings from versions of the phylogenetic Shapley value agree on ultrametric trees

Let $T^r$ be a rooted phylogenetic tree with leaf set $X$, $|X|=n$, and edge lengths $\lambda_e\ge0$. The rooted phylogenetic diversity $PD^r(S)$ of $S\subseteq X$ is the total length of the smallest subtree containing $S$ and the root (so $PD^r(\{a\})$ is the root-to-leaf distance of $a$); for the unrooted tree $T^u$, $PD^u(S)$ is the length of the subtree spanning $S$, with $PD^u(\{a\})=0$. Three versions of the Shapley value of taxon $a$ are used to rank species for conservation:

- the **original Shapley value** of the cooperative game $PD^r$,

$$SV_{T^r}(a)=\frac1{n!}\sum_{S\ni a}(|S|-1)!\,(n-|S|)!\,\bigl(PD^r(S)-PD^r(S\setminus\{a\})\bigr),$$

which equals the **Fair Proportion index** $FP_{T^r}(a)=\sum_{e}\lambda_e/D_e$ (sum over edges on the path from $a$ to the root, $D_e$ the number of leaves below $e$);
- the **modified Shapley value** $\widetilde{SV}_{T^r}(a)$, the same sum restricted to coalitions with $|S|\ge2$;
- the **unrooted Shapley value on rooted trees** $\widehat{SV}_{T^r}(a)=SV_{T^u}(a)$, the original Shapley value of the game $PD^u$ on the unrooted tree.

**Proposition.** If $T^r$ is a rooted binary ultrametric tree (all leaves at the same distance $h$ from the root), then the rankings of the taxa induced by $SV_{T^r}$ and by $\widetilde{SV}_{T^r}$ are identical.

In general the three versions differ, and the differences can be made arbitrarily large or arbitrarily small by choosing edge lengths: on a four-taxon tree with a parameter $\varepsilon$, $|SV-\widetilde{SV}|=\frac1{4\varepsilon}+\frac\varepsilon4\to\infty$ as $\varepsilon\to0$ while $|\widehat{SV}-\widetilde{SV}|=\frac\varepsilon2\to0$. In simulations, the probability that two versions give exactly the same ranking decreases with the number of taxa, while a normalized distance between the rankings tends to zero.

## Expansion

The only coalition counted in $SV$ but not in $\widetilde{SV}$ is $S=\{a\}$, which carries weight $0!\,(n-1)!/n!=1/n$ and marginal contribution $PD^r(\{a\})-PD^r(\emptyset)=PD^r(\{a\})$. Hence

$$SV_{T^r}(a)-\widetilde{SV}_{T^r}(a)=\frac{PD^r(\{a\})}{n},$$

the root-to-leaf distance of $a$ divided by $n$. On an ultrametric tree this equals $h/n$ for every taxon, so $\widetilde{SV}$ is $SV$ shifted by a constant and the two rankings coincide, ties included. On non-ultrametric trees the shift varies across taxa, so taxa on long root-to-leaf paths are favored more by $SV$ (equivalently by Fair Proportion) than by $\widetilde{SV}$, which can reorder them. The unrooted version differs further because $PD^u$ ignores the path to the root.

## Sources

- Kristina Wicke, Mareike Fischer, "Comparing the rankings obtained from two biodiversity indices: the Fair Proportion Index and the Shapley Value", arXiv (2015). Section 2 (Definitions 2–5, Theorem 1 after Fuchs and Jin, Example 6), Section 3 (Proposition 1, simulation results). <https://doi.org/10.48550/arXiv.1507.08620>. Published version: Journal of Theoretical Biology 430 (2017), 207–214, <https://doi.org/10.1016/j.jtbi.2017.07.010>; locators above refer to the arXiv version.
