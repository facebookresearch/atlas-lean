# Majority-rule (+) supertree

**Splits and medians.** A profile $P = (t_1, \dots, t_k)$ is a list of unrooted phylogenetic trees with leaf sets $\mathcal L(t_i)$, and $\mathcal L(P) = \bigcup_i \mathcal L(t_i)$. A tree displays a split $A|B$ if deleting some edge separates $A$ from $B$; $\mathrm{Spl}(T)$ is the set of nontrivial full splits of $T$, and $d(T, T') = |\mathrm{Spl}(T) \,\triangle\, \mathrm{Spl}(T')|$ is the symmetric-difference (Robinson–Foulds) distance. For trees on a common leaf set, the majority-rule consensus $\mathrm{Maj}(P)$ displays exactly the splits present in more than $k/2$ of the trees; it is a median tree, i.e. it minimizes $\mathrm{dist}(T,P) = \sum_i d(T, T_i)$, and it is the strict consensus of all median trees. The score of a profile is $s(P) = \min_T \mathrm{dist}(T,P)$.

**Definition.** The span $\langle t\rangle$ of an input tree is the set of all trees on $\mathcal L(P)$ that display $t$. A representative selection is a tuple $R = (T_1, \dots, T_k)$ with $T_i \in \langle t_i\rangle$; $\mathrm{Maj}(R)$ is a candidate supertree, and it is optimal if $s(R)$ is minimum over all representative selections. The **majority-rule (+) supertree** $\mathrm{Maj}^+(P)$ is the strict consensus of all optimal candidate supertrees.

**Theorem.**
1. (Consensus case.) When all input trees share one leaf set, $\mathrm{Maj}^+(P)$ is exactly the tree displaying every split that is displayed by more input trees than are incompatible with it; it is an optimal candidate tree and the strict consensus of all optimal candidate trees, hence computable in polynomial time.
2. (Hardness.) Unless $\mathrm{P} = \mathrm{NP}$, no polynomial-time algorithm constructs an optimal candidate supertree for profiles with partially overlapping leaf sets.
3. (Reduction to restricted selections.) Restricting each $t_i$'s completion to a minimal fill-in, $\mathrm{Maj}^+(P)$ equals the strict consensus of $\{\mathrm{Maj}^+(G)\}$ over the restricted representative selections $G$ of minimum adjusted score (the score of the completion of $G$). This yields an exact integer linear program over fill-in variables of the profile's split matrix.

## Expansion

Hardness follows from quartet compatibility: a set of quartets is compatible iff the profile consisting of those quartets has an optimal candidate supertree of score $0$, since any tree displaying all quartets lies in every span. Part 3 shows the search can be confined to selections that add only the splits forced by the consensus, which is what makes the ILP finite and practical (exact solutions up to about 40 taxa). A data-reduction rule scales it further: a set $S$ of taxa that every input tree separates from the rest by some split (a reducible set) can be solved as a satellite profile on $S$ and a reduced profile in which $S$ is a single supertaxon, then grafted back. In contrast with plain majority-rule consensus, the method keeps resolution contributed by a single specialist input tree unless the other trees actively contradict it.

## Sources

- J. Dong, D. Fernández-Baca, F. R. McMorris, "Constructing majority-rule supertrees", Algorithms for Molecular Biology 5:2 (2010), Theorems 1–5 and Lemma 1, <https://doi.org/10.1186/1748-7188-5-2>, PMCID PMC2826330.
