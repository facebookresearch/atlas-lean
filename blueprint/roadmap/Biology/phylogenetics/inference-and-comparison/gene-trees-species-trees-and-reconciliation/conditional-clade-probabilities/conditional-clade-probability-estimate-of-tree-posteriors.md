# Conditional clade probability estimate of tree posteriors

**Setting.** Let $X$ be a finite set of taxa and let $T_1, \dots, T_N$ be rooted binary trees on $X$ sampled from a posterior distribution (for example, gene trees sampled by MCMC under a sequence-evolution model). A **clade** is the leaf set $\gamma \subseteq X$ below a node; each internal node splits its clade $\gamma$ into an unordered pair $\{\gamma', \gamma \setminus \gamma'\}$. For a clade $\gamma$ with $|\gamma| \ge 2$ and a split $\{\gamma', \gamma\setminus\gamma'\}$, define the **conditional clade frequency**

$$\hat P(\gamma', \gamma \setminus \gamma' \mid \gamma) = \frac{\#\{i : T_i \text{ contains } \gamma \text{ split as } \{\gamma', \gamma\setminus\gamma'\}\}}{\#\{i : T_i \text{ contains } \gamma\}} .$$

**Definition (CCP estimate).** For any rooted binary tree $T$ on $X$ whose clades all occur in the sample (a tree that can be **amalgamated** from the sample), its posterior probability is estimated by

$$\hat P(T) = \prod_{\gamma \in \mathcal{C}(T),\ |\gamma| \ge 2} \hat P(\text{split of } \gamma \text{ in } T \mid \gamma),$$

where $\mathcal{C}(T)$ is the set of clades of $T$.

**Properties.**

1. $\hat P$ is a probability distribution on the set of amalgamable trees: summing $\hat P$ over all of them gives one, because at every clade the conditional frequencies over its observed splits sum to one.
2. $\hat P$ is exact when the posterior over trees has the conditional-independence structure it assumes: the split of a clade is independent of how the rest of the tree is resolved, given that the clade is present.
3. The set of amalgamable trees can be much larger than the set of distinct sampled trees, and sums or maximizations of $\hat P(T)\,g(T)$ for any score $g$ that factorizes over clades (such as a reconciliation likelihood computed by dynamic programming over clades) can be computed exactly by a recursion over the observed clades, ordered by size, without enumerating trees.

## Expansion

Write a rooted binary tree as the sequence of splits obtained by recursively splitting $X$. The posterior factorizes as a product of conditional probabilities of each split given the clade being split, if the subtree resolutions of disjoint clades are conditionally independent; the CCP estimate replaces each factor by its sample frequency. Summing the product over all choices of observed splits, from the leaves upward, collapses each clade's contribution to one, which gives property 1. Because the counts are pooled across trees, a split observed in one sampled tree can be combined with a split of a different clade observed in another, which is why amalgamation explores trees never sampled. In gene-tree/species-tree reconciliation (amalgamated likelihood estimation), the joint score of a gene tree is $\hat P(T)$ times the probability of $T$ under a duplication–transfer–loss model along the species tree; both factor over clades, so the most probable reconciled gene tree among all amalgamable trees is found by one dynamic program.

## Sources

- Szöllősi GJ, Tannier E, Daubin V, Boussau B, "The inference of gene trees with species trees" (2015), section on amalgamation of reconciled gene trees and Figure 6 (conditional clade probabilities and amalgamated likelihood estimation), <https://doi.org/10.1093/sysbio/syu048>, PMCID PMC4265139.
- S. Höhna and A. J. Drummond, "Guided tree topology proposals for Bayesian phylogenetic inference", Systematic Biology 61 (2012) 1–11, <https://doi.org/10.1093/sysbio/syr074>.
- B. Larget, "The estimation of tree posterior probabilities using conditional clade probability distributions", Systematic Biology 62 (2013) 501–511, <https://doi.org/10.1093/sysbio/syt014>.
