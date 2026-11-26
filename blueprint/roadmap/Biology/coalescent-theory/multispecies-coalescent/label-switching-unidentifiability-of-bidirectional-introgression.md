# Label-switching unidentifiability of bidirectional introgression

Consider the MSci model of two species $A$ and $B$ with root $R$ and **bidirectional introgression** at a common time $\tau_X$. Going backward in time, lineages of $A$ reach a hybridization node $X$ with parental populations $XR$ (the vertical path, probability $\varphi_X$) and $YR$ (the horizontal path into $B$'s side, probability $1 - \varphi_X$). Lineages of $B$ reach a node $Y$ with vertical parent $YR$ (probability $\varphi_Y$) and horizontal parent $XR$ (probability $1 - \varphi_Y$). The populations $XR$ and $YR$, with sizes $\theta_X$ and $\theta_Y$, persist until the root at $\tau_R$. Write

$$\Theta = (\theta_A, \theta_B, \theta_R, \theta_X, \theta_Y, \tau_R, \tau_X, \varphi_X, \varphi_Y), \qquad \Theta' = (\theta_A, \theta_B, \theta_R, \theta_Y, \theta_X, \tau_R, \tau_X, 1 - \varphi_X, 1 - \varphi_Y).$$

For a flagged gene tree $G$ (topology, coalescence times and the left/right flags of each branch at $X$ and $Y$, as in the gene-tree density), let $\mathrm{swap}(G)$ be the same tree with the flags exchanged, $l \leftrightarrow r$, at both $X$ and $Y$, so that every segment it placed in $XR$ is placed in $YR$ and conversely. Write $\bar G$ for the unflagged tree (topology and coalescence times) and $\bar f(\bar G \mid \Theta) = \sum_{G \mapsto \bar G} f(G \mid \Theta)$ for its density, the sum running over the flag assignments compatible with $\bar G$.

**Claim.** For every flagged gene tree $G$ and every sample configuration $(n_A, n_B)$,

$$f(G \mid \Theta) = f(\mathrm{swap}(G) \mid \Theta').$$

Since $\mathrm{swap}$ is a bijection on the flag assignments compatible with $\bar G$, also $\bar f(\bar G \mid \Theta) = \bar f(\bar G \mid \Theta')$ for every unflagged gene tree; the sequence likelihood depends on $\bar G$ alone, so the likelihood of any sequence data $X$ is the same at $\Theta$ and $\Theta'$. Hence $\Theta$ is not identifiable even from gene trees with coalescence times and multiple sequences per species. If moreover the whole joint prior is invariant under $\Theta \mapsto \Theta'$, that is, $f(\Theta) = f(\Theta')$ (which requires invariance under the exchange $\theta_X \leftrightarrow \theta_Y$ together with $\varphi \mapsto 1 - \varphi$; independent identically distributed priors on $\theta_X, \theta_Y$ and independent symmetric $\mathrm{Beta}(\alpha, \alpha)$ priors on $\varphi_X, \varphi_Y$ suffice, while symmetric beta marginals alone do not), then the posterior satisfies $f(\Theta \mid X) = f(\Theta' \mid X)$ for all data $X$. An identifiability constraint such as $\varphi_X < 1/2$ removes the symmetry.

## Proof sketch

Under $\Theta$ a lineage from $A$ that takes the left (vertical) path at $X$ contributes $\varphi_X$ and then coalesces in $XR$ at rate $2/\theta_X$. In $\mathrm{swap}(G)$ under $\Theta'$ that lineage takes the right (horizontal) path, contributing $1 - \varphi'_X = \varphi_X$, and enters $YR$, where it coalesces at rate $2/\theta'_Y = 2/\theta_X$. The same holds for a lineage taking the right path at $X$, and for lineages from $B$ at $Y$. A fixed flag is not enough: holding a left flag fixed gives the factor $\varphi_X$ under $\Theta$ but $1 - \varphi_X$ under $\Theta'$, which is why the identity pairs $G$ with $\mathrm{swap}(G)$. So the factor-by-factor form of the gene-tree density matches: the flag factors agree, and each interval in $XR$ under $\Theta$ becomes the same interval, with the same number of lineages and the same size parameter, in $YR$ under $\Theta'$, and conversely. The populations $A$, $B$, $R$ and the times are untouched. Summing over flags gives the unflagged identity, and Bayes' formula with $f(\Theta) = f(\Theta')$ gives equal posterior densities: the posterior has "twin towers" of equal height. A related, more elementary unidentifiability holds whenever at most one sequence per locus is sampled below a population: its $\theta$, and the times of hybridization events whose parental populations then hold at most one lineage, do not enter the gene-tree density.

## Depends on

- [Gene-tree density under the multispecies coalescent with introgression](multispecies-coalescent-with-introgression-gene-tree-density.md)

## Sources

- T. Flouri, X. Jiao, B. Rannala and Z. Yang, "A Bayesian implementation of the multispecies coalescent model with introgression for phylogenomic analysis", Molecular Biology and Evolution (2020; online 2019), Discussion ("Identifiability of MSci Models") and Materials and Methods (third simulation set, model D), <https://doi.org/10.1093/molbev/msz296>, PMCID PMC7086182.
