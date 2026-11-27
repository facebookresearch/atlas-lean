# Linear lower bound on the variance of internode distance under the multispecies coalescent

**Model.** A species tree $(\mathcal S,\Gamma)$ is a rooted binary tree on species $\{1,\ldots,n\}$ with branch lengths $\Gamma$ in coalescent time units (not necessarily ultrametric). Under the multispecies coalescent (MSC), each of $m$ unlinked genes has a gene tree generated backwards in time: within each branch every pair of lineages coalesces at rate $1$, lineages of sister populations are pooled where branches merge, and one individual is sampled per species. Write $\{\mathcal T_j\}_{j=1}^m \sim \mathcal D_s^m[\mathcal S,\Gamma]$ for $m$ i.i.d. unrooted gene tree topologies (assumed known without error).

**Internode distance.** For species $x,y$, let $d_g^{\mathcal T_j}(x,y)$ be the number of edges on the path between $x$ and $y$ in $\mathcal T_j$, and

$$\hat\delta_{\mathrm{int}}^m(x,y) = \frac{1}{m}\sum_{j=1}^m d_g^{\mathcal T_j}(x,y).$$

Its expectation $\bar\delta_{\mathrm{int}}(x,y)$ is an additive tree metric on the unrooted species tree $\mathcal S_u$, which is the basis of NJst, ASTRID and related distance methods.

**Theorem.** There are constants $C, f_0>0$ such that for every integer $n\ge 4$ and every $f\in(0,f_0]$ there is a species tree $(\mathcal S,\Gamma)$ with $n$ leaves and shortest branch length $f$ such that, for all pairs of species $\ell,\ell'$ and all $m\ge 1$,

$$\mathrm{Var}\big[\hat\delta_{\mathrm{int}}^m(\ell,\ell')\big] \ge C\,\frac{d_g^{\mathcal S_u}(\ell,\ell')}{m},$$

where $d_g^{\mathcal S_u}$ is graph distance in the unrooted species tree, and consequently

$$\max_{\ell,\ell'}\mathrm{Var}\big[\hat\delta_{\mathrm{int}}^m(\ell,\ell')\big] \ge C\,\frac{n}{m}.$$

## Depends on

- [The multispecies coalescent](../../../coalescent-theory/multispecies-coalescent/gene-tree-prob.md)
- [Rooted binary species tree with branch lengths](../../../coalescent-theory/multispecies-coalescent/species-tree.md)

## Expansion

The extremal species tree is a caterpillar whose backbone alternates *short* branches of length $f$ and *long* branches. Short branches create local uncertainty in how many lineages coalesce onto the path between two leaves; long branches make essentially all lineages coalesce within each block, so the block contributions to the internode distance are nearly independent. The proof chains four estimates: by independence of genes, $\mathrm{Var}[\hat\delta_{\mathrm{int}}^m] = \frac1m \mathrm{Var}[d_g^{\mathcal T_1}]$; full coalescence in all blocks has probability at least $1-1/n$; on that event the gene-tree distance is a sum of about $(n-2)/2$ i.i.d. block contributions, giving $\mathrm{Var}[d_g^{\mathcal T_1}] \ge \frac{n-2}{2}\,\mathrm{Var}[X_1\mid \text{block coalesces}]\,\mathbb P[\text{all blocks coalesce}]$; and each block contributes

$$\mathrm{Var}[X_1\mid \text{block coalesces}] = \tfrac13 e^{-f}\big(1-\tfrac13 e^{-f}\big) = \tfrac29\,(1-\Theta(f)).$$

*Implications.* Making all variances negligible requires the number of genes $m$ to grow at least linearly in $n$ for methods that use all pairwise distances (such as NJst, based on Neighbor-Joining), whereas certain quartet-based methods (ASTRAL) have sample complexity logarithmic in $n$. Fast-converging methods that use only distances up to the tree depth, at most of order $\log n$ in graph distance, are not affected by the $n/m$ bound. The theorem bounds the variance only; correlations between internode distances computed from the same gene trees may produce cancellations, so it does not by itself give a sample-complexity lower bound.

## Sources

- Sébastien Roch, "On the Variance of Internode Distance Under the Multispecies Coalescent", in Lecture Notes in Computer Science (2018), 196–206, <https://doi.org/10.1007/978-3-030-00834-5_11>. Published version of arXiv:1812.08357, cited next; locators there refer to the arXiv version.
- Sebastien Roch, "On the variance of internode distance under the multispecies coalescent", arXiv:1812.08357 (2018), Section 2 (multispecies coalescent, internode distance, Theorem 1) and Section 4 (Lemmas 1-4), <https://doi.org/10.48550/arXiv.1812.08357>.
