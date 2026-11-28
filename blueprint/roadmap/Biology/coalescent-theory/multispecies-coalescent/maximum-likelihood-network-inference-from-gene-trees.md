# Maximum-likelihood inference of phylogenetic networks from gene trees, and nesting of network models

Let $\Psi$ be a species network (topology and branch lengths in coalescent units) and $\Gamma$ an $|E(\Psi)| \times m$ matrix of inheritance probabilities for $m$ independent loci, with $\Gamma(b,j) \in [0,1]$, $\Gamma(b,j) = 1$ for an edge $b$ into a tree node, and $\Gamma(b,j) + \Gamma(b',j) = 1$ for the two edges $b, b'$ into a reticulation. Gene genealogies arise under the network multispecies coalescent.

**Likelihoods.** From sequence alignments $S_1, \dots, S_m$,

$$L(\Psi, \Gamma \mid S) = \prod_{i=1}^{m} \int P(S_i \mid g)\, p(g \mid \Psi, \Gamma)\, dg,$$

with gene-tree branch lengths converted from substitutions per site to coalescent units by the factor $2/\theta$, $\theta = 4N_e u$. From estimated genealogies $G_1, \dots, G_m$ (topologies, or topologies with branch lengths),

$$L(\Psi, \Gamma \mid G) = \prod_{i=1}^{m} p(G_i \mid \Psi, \Gamma),$$

and if locus $i$ is represented by a set $\mathcal{G}_i$ of bootstrap genealogies, $p(G_i \mid \Psi, \Gamma)$ is replaced by $|\mathcal{G}_i|^{-1}\sum_{g \in \mathcal{G}_i} p(g \mid \Psi, \Gamma)$.

**Proposition (nesting).** Let $\Omega(n, k)$ be the networks on $n$ taxa with $k$ reticulations. For every $(\Psi, \Gamma)$ with $\Psi \in \Omega(n,k)$ there is $(\Psi', \Gamma')$ with $\Psi' \in \Omega(n, k+1)$ inducing the same distribution of gene genealogies, hence

$$\sup_{\Psi' \in \Omega(n,k+1),\,\Gamma'} L(\Psi', \Gamma') \ \ge\ \sup_{\Psi \in \Omega(n,k),\,\Gamma} L(\Psi, \Gamma).$$

The maximum likelihood is non-decreasing in the number of reticulations, so the number of reticulations cannot be chosen by likelihood alone; information criteria or cross-validation on held-out gene tree frequencies are used instead.

## Depends on

- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](network-multispecies-coalescent-fixed-network-ge.md)
- [Gene tree topology probabilities on a phylogenetic network via MUL-trees and allele mappings](gene-tree-topology-probability-on-a-network-via-mul-trees.md)

## Expansion

To embed $\Psi$ in $\Omega(n, k+1)$, subdivide two edges with new vertices $u$ (on an edge $e_1$) and $w$ (on an edge $e_2$, not below $u$ so that no cycle is created), and add the arc $(u, w)$, which makes $w$ a reticulation. Set the inheritance probability of $(u,w)$ to $0$ and of the subdivided half of $e_2$ entering $w$ to $1$ at every locus. Every lineage then follows the original edges, the subdivided branches have the original total lengths, and the genealogy distribution is unchanged. The product forms of the likelihoods come from independence of loci given the species history; the bootstrap average integrates gene tree estimation uncertainty approximately. With fully resolved topologies, $K$-fold cross-validation compares predicted and held-out gene tree frequencies, accepting an extra reticulation only for a substantial improvement in fit (3% in the paper).

## Sources

- Y. Yu, J. Dong, K. J. Liu and L. Nakhleh, "Maximum likelihood inference of reticulate evolutionary histories", Proceedings of the National Academy of Sciences 111 (2014), 16448–16453, Equations 1–3 and the sections "Maximum Likelihood Inference" and "Controlling for Model Complexity", <https://doi.org/10.1073/pnas.1407950111> (PMC4246314).
