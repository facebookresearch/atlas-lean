# Uniqueness of the Markov blanket of disease status

Let $V$ be a finite set of discrete random variables consisting of SNP genotypes and a disease status $T$, with joint distribution $J$, and let $G$ be a directed acyclic graph on $V$ such that $J$ satisfies the Markov condition for $G$ (each variable is independent of its non-descendants given its parents), so that $J(x_1,\dots,x_n) = \prod_i J(x_i \mid \mathrm{Pa}(x_i))$. A *Markov blanket* of $T$ is a minimal set $\mathrm{MB}(T) \subseteq V\setminus\{T\}$ such that $T \perp X \mid \mathrm{MB}(T)$ for every $X \in V\setminus(\mathrm{MB}(T)\cup\{T\})$. The pair $(G, J)$ is *faithful* if every conditional independence that holds in $J$ is entailed by the Markov condition on $G$.

If $(G,J)$ is faithful, then $\mathrm{MB}(T)$ is unique and equals the set of parents of $T$, children of $T$ and other parents of children of $T$ in $G$. In particular, the conditional law of disease status given all genotypes depends only on the SNPs in $\mathrm{MB}(T)$, and a SNP with no marginal association can still belong to $\mathrm{MB}(T)$ as a co-parent of an interaction, which is why Markov-blanket search can detect epistatic SNP sets.

## Depends on

- [Markov Blanket](../../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/bayesian-networks/markov-blanket.md)
- [Joint distribution of a Bayesian network](../../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/bayesian-networks/joint-2.md)
- [d-separation](../../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/causal-bayesian-networks/dseparated.md)

## Proof depends on

- [The Markov blanket d-separates a node from all other nodes](../../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/bayesian-networks/d-separated-markov-blanket.md)
- [Completeness of d-separation](../../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/bayesian-networks/exists-not-cond-indep-of-not-d-separated.md)

## Expansion

The parents, children and spouses of $T$ d-separate $T$ from every other node, so by the Markov condition they form a blanket. Under faithfulness a node adjacent to $T$ is dependent on $T$ given every subset of the other variables, and a spouse is dependent on $T$ given any set containing the common child, so no proper subset of this set can shield $T$; hence every Markov blanket contains it and the minimal one is unique. Algorithms such as IAMB and its variants grow a candidate blanket by adding the variable most dependent on $T$ given the current blanket and then remove variables that become conditionally independent, using a test such as the $G^2$ conditional-independence test.

## Sources

- B. Han, M. Park and X.-W. Chen, "A Markov blanket-based method for detecting causal SNPs in GWAS", BMC Bioinformatics 11 (Suppl. 3) (2010), S5, <https://doi.org/10.1186/1471-2105-11-S3-S5>, PMCID PMC2863064. Definition 1 and Theorem 1; the theorem is due to J. Pearl, *Probabilistic Reasoning in Intelligent Systems* (1988), and I. Tsamardinos and C. F. Aliferis (2003).
