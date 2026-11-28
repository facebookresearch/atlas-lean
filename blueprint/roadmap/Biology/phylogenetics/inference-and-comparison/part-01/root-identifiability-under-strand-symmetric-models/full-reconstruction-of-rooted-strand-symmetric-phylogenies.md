# Full reconstruction of rooted strand-symmetric phylogenies

**Setting.** A Markov model on a tree has root distribution $\pi$ and edge transition matrices $P^{uv}$ (child $v$ further from the root than $u$); the root may have degree $1$, $2$ or $3$ and all other internal nodes have degree $3$. A set $\mathcal M$ of matrices is *reconstructible from rows* if $RM\notin\mathcal M$ for every $M\in\mathcal M$ and permutation matrix $R\ne I$ (e.g. matrices whose diagonal is the largest entry of each column). The set $\mathcal S(\mathcal M)$ *sympathetic* to $\mathcal M$ contains all $M$ with $RM\notin\mathcal M$ for every $R\ne I$; it includes long-branch matrices that are not themselves in $\mathcal M$. Strand symmetry and compositional asymmetry are as in the two-taxon lemma.

**Theorem.**

1. *(Rooted topology.)* Assume (A) every internal node distribution $\pi^m$ is compositionally asymmetric and, for each edge, (B) $P^{uv}$ is invertible, (C) not a permutation matrix, and (D) strand-symmetric. Then the *rooted* topology is identifiable from the pairwise joint distributions of states at the leaves.
2. *(Full model.)* If in addition (E) from every internal node there is a path to a leaf whose edge matrices lie in $\mathcal M$, and (F) every edge matrix lies in $\mathcal S(\mathcal M)$, then the topology, root position, root distribution and all transition matrices are identifiable from the joint leaf distribution, already for two or more leaves.
3. *(Continuous time.)* The same holds if each $P^{uv}$ has a unique logarithm $Q^{uv}=\log P^{uv}$ with non-negative off-diagonal entries and $Q^{uv}$ (instead of $P^{uv}$) is strand-symmetric.
4. *(Consistency of maximum likelihood.)* If $\mathcal M$ is *strongly* reconstructible from rows ($RM\notin\overline{\mathcal M}$) and the long-branch class is *strongly* sympathetic (a ball around each $RM$ misses $\mathcal M$), then the maximum likelihood estimator of topology, root distribution and edge matrices (or rate matrices, in continuous time) is strongly consistent as the number of independent sites grows.

## Expansion

Standard reversible models such as GTR, and even the general Markov model, cannot place the root or be fitted to fewer than three sequences: reversibility makes the likelihood invariant under moving the root, and hidden-state labels are only determined up to permutation. Here every cherry is identifiable up to $8$ relabellings by the two-taxon lemma, pairwise leaf distributions then give the unrooted topology (invertible non-permutation edges), and non-stationary composition orients it. The remaining label ambiguity at internal nodes is resolved by requiring a path of "short" edges (in $\mathcal M$) from each internal node to a leaf, while sympathy allows other edges to be long. Consistency follows from identifiability via a Wald-type argument for finite sample spaces with a compact parameter closure; the strong versions of the conditions keep the parameter set away from its non-identifiable boundary.

## Depends on

- [Two-taxon identifiability of non-stationary strand-symmetric Markov models](two-taxon-identifiability-of-non-stationary-strand-symmetric-markov-models.md)

## Proof depends on

- [Uniform law of large numbers for the log-likelihood](../../../consistency-of-the-gtr-maximum-likelihood-estima/ae-tendsto-uniformly-log-lik-empirical-f.md)
- [Wald's argmax theorem](../../../consistency-of-the-gtr-maximum-likelihood-estima/tendsto-inf-dist-of-tendsto-uniformly.md)

## Sources

- Benjamin D. Kaehler, "Full Reconstruction of Non-Stationary Strand-Symmetric Models on Rooted Phylogenies", arXiv:1610.05057 (2016), Section 3: Proposition 3.1, Corollary 3.1, Definitions 3.3–3.4, Theorems 3.1–3.2; Section 4: Definitions 4.1–4.2, Theorems 4.1–4.2 and Lemma 4.1, <https://doi.org/10.48550/arXiv.1610.05057>.
