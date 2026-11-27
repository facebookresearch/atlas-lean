# Localized haplotype-cluster model and its induced haplotype HMM

Fix $M$ biallelic or multiallelic markers and a finite multiset $\mathcal H$ of complete haplotypes $h = (h_1,\dots,h_M)$. A **localized haplotype-cluster model** for $\mathcal H$ is a directed acyclic multigraph $G$ such that

1. $G$ has a unique root node (no incoming edges) and a unique terminal node (no outgoing edges);
2. $G$ is *leveled* with levels $0,1,\dots,M$: every edge goes from a node at level $m-1$ to a node at level $m$, the root has level $0$ and the terminal node level $M$;
3. every edge whose child node is at level $m$ is labeled with an allele of marker $m$, and two edges with the same parent node carry different labels;
4. for every $h \in \mathcal H$ there is a root-to-terminal path whose $m$-th edge is labeled $h_m$ (by 3 this path is unique), and every edge is traversed by at least one $h \in \mathcal H$.

Each edge $e$ is a *localized haplotype cluster*: the set of haplotypes whose path traverses $e$. Write $n(e)$ for the number of haplotypes traversing $e$ and $n_p(e)$ for the number traversing the parent node of $e$. Let $L_m$ be the set of edges whose child node is at level $m$.

**Induced HMM.** $G$ defines a hidden Markov model whose hidden state at marker $m$ is an edge $e \in L_m$ and whose emitted symbol is the label of $e$ (emitted with probability $1$). Its initial and transition probabilities are

$$P(e) = \frac{n(e)}{n_p(e)} \ \text{if the parent of } e \text{ is the root, } 0 \text{ otherwise},$$

$$P(e_1 \mid e_2) = \frac{n(e_1)}{n_p(e_1)} \ \text{if the parent node of } e_1 \text{ is the child node of } e_2, \ 0 \text{ otherwise}.$$

Each row is a probability vector because the counts of the outgoing edges of a node sum to the node count. Transition probabilities depend on $e_2$ only through its child node, so edges merging into a common node (which model historical recombination) share their future: given the cluster at marker $m$, the alleles at markers $m+1, m+2, \dots$ are independent of the alleles at markers $m, m-1, \dots$ (the Markov property defining the clusters).

## Expansion

Property 3 makes the path of a haplotype unique, so the probability the HMM assigns to a haplotype in $\mathcal H$ is the product of the conditional frequencies $n(e)/n_p(e)$ along its path, i.e. the empirical frequency of $h$ factorized through the local clusters. Unlike fixed-$K$ cluster models, the number of clusters $|L_m|$ varies with $m$ and adapts to local linkage disequilibrium.

## Sources

- S. R. Browning and B. L. Browning, "Rapid and Accurate Haplotype Phasing and Missing-Data Inference for Whole-Genome Association Studies By Use of Localized Haplotype Clustering", The American Journal of Human Genetics 81 (2007), 1084–1097, <https://doi.org/10.1086/521987> (PMC2265661). Methods, sections "The Localized Haplotype-Cluster Model" and "The Induced HMM".
