# Compatible mutation patterns as a minimum-weight vertex cover

**Patterns and compatibility.** Let $S$ be the set of tumour samples of one patient. A mutation pattern is a subset $v \subseteq S$ (a binary vector of length $\lvert S\rvert$), the samples in which a variant is present. Two patterns $v, v'$ are *compatible* if they are nested or disjoint, and *incompatible* otherwise. With the normal sample as root (carrying no somatic variant), a family of patterns is realized by a rooted tree in which each pattern is the set of samples below one edge if and only if the family is pairwise compatible.

**Pattern likelihoods.** For each variant $\mu$ and sample $s$, let $p_{\mu,s}$ and $q_{\mu,s} = 1 - p_{\mu,s}$ be posterior probabilities that $\mu$ is present or absent in $s$, obtained from a binomial model of $K$ variant reads among $N$ with sequencing error, a prior with an atom at zero variant frequency, and a sample-specific absence threshold depending on the sample's neoplastic cell content. Assuming independence across samples, the likelihood that $\mu$ has pattern $v$ is

$$L_\mu(v) = \prod_{s \in S} p_{\mu,s}^{\,v_s}\, q_{\mu,s}^{\,1 - v_s},$$

and assuming independence across the $m$ variants, $\prod_\mu (1 - L_\mu(v))$ is the probability that *no* variant has pattern $v$. The reliability score of $v$ is

$$\omega_v = -\log \prod_{\mu = 1}^{m}\bigl(1 - L_\mu(v)\bigr),$$

normalized by $m$ in practice.

**Proposition (vertex-cover formulation).** Build the *evolutionary conflict graph* $G = (V, E)$ whose vertices are the $2^{\lvert S\rvert}$ patterns, with an edge between each incompatible pair, and weight vertex $i$ by $c_i = \omega_i \ge 0$. A set $X \subseteq V$ covers every edge if and only if $V \setminus X$ is pairwise compatible. Therefore the most reliable compatible family, the compatible family of maximum total reliability, is the complement of a minimum-weight vertex cover, i.e. of an optimal solution of

$$\min \sum_{i \in V} c_i x_i \quad \text{subject to}\quad x_i + x_j \ge 1 \ \ \forall (i, j) \in E, \qquad x_i \in \{0, 1\}.$$

Once $\{i : x_i = 0\}$ is fixed, each variant is assigned to its most likely compatible pattern and the unique tree realizing the family is built in time quadratic in the input size. The source proves that the selection problem is equivalent to minimum vertex cover, hence NP-hard, and that no polynomial-time approximation with ratio better than $1.3606$ exists unless $\mathrm{P} = \mathrm{NP}$.

## Depends on

- [Compatible clusters are nested or disjoint](../../../phylogenetics/splits-compatibility-ultrametrics-and-upgma/compatible-iff-nested-or-disjoint.md)
- [Perfect phylogeny and the four-gamete condition](../../../phylogenetics/splits-compatibility-ultrametrics-and-upgma/exists-perfect-phylogeny-iff.md)

## Expansion

A set $X$ is a vertex cover exactly when no edge has both ends outside $X$, i.e. when $V \setminus X$ is an independent set of $G$, which by construction is a pairwise compatible family. Total weight is fixed, so minimizing the weight of $X$ maximizes the weight of the retained compatible family. A pairwise nested-or-disjoint family of subsets of $S$ is a hierarchy, and hierarchies are exactly the cluster systems of rooted trees, which gives the tree. The reliability score is large when some variant is confidently assigned to $v$ (any $L_\mu(v)$ near $1$ makes $1 - L_\mu(v)$ near $0$), and accumulates weak support from many variants, so uncertain presence calls in low-purity or low-coverage samples lower all pattern likelihoods instead of forcing a hard call. The inapproximability bound is the Dinur–Safra bound for vertex cover transferred through the equivalence; integer linear programming nevertheless solves instances of this size exactly. Highly reliable patterns that remain in conflict can indicate mixed samples containing subclones with distinct evolutionary histories.

## Sources

- J. G. Reiter, A. P. Makohon-Moore, J. M. Gerold, I. Bozic, K. Chatterjee, C. A. Iacobuzio-Donahue, B. Vogelstein, M. A. Nowak, *Reconstructing metastatic seeding patterns of human cancers*, Nature Communications 8 (2017), 14114, <https://doi.org/10.1038/ncomms14114>, PMCID PMC5290319. Methods, "Bayesian inference model" (posterior presence and absence probabilities, pattern likelihood, reliability score), "Identifying evolutionarily compatible mutation patterns" (conflict graph, integer program, equivalence with minimum vertex cover; inapproximability stated there and proved in Supplementary Methods, Theorem 1), and "Inferring evolutionary trees".
- I. Dinur, S. Safra, *On the hardness of approximating minimum vertex cover*, Annals of Mathematics 162 (2005), 439–485, <https://doi.org/10.4007/annals.2005.162.439>.
