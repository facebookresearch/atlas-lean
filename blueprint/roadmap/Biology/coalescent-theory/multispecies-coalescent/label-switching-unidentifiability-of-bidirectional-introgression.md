# Label-switching unidentifiability of bidirectional introgression

Consider the MSci model of two species $A$ and $B$ with root $R$ and **bidirectional introgression** at a common time $\tau_X$. Going backward in time, lineages of $A$ reach a hybridization node $X$ with parental populations $XR$ (the vertical path, probability $\varphi_X$) and $YR$ (the horizontal path into $B$'s side, probability $1 - \varphi_X$). Lineages of $B$ reach a node $Y$ with vertical parent $YR$ (probability $\varphi_Y$) and horizontal parent $XR$ (probability $1 - \varphi_Y$). The populations $XR$ and $YR$, with sizes $\theta_X$ and $\theta_Y$, persist until the root at $\tau_R$. Write

$$\Theta = (\theta_A, \theta_B, \theta_R, \theta_X, \theta_Y, \tau_R, \tau_X, \varphi_X, \varphi_Y), \qquad \Theta' = (\theta_A, \theta_B, \theta_R, \theta_Y, \theta_X, \tau_R, \tau_X, 1 - \varphi_X, 1 - \varphi_Y).$$

**Claim.** $f(G \mid \Theta) = f(G \mid \Theta')$ for every gene tree $G$ and every sample configuration $(n_A, n_B)$. Hence $\Theta$ is not identifiable even from gene trees with coalescence times and multiple sequences per species, and under symmetric priors $\varphi_X, \varphi_Y \sim \mathrm{Beta}(\alpha, \alpha)$ the posterior satisfies $f(\Theta \mid X) = f(\Theta' \mid X)$ for all data $X$. An identifiability constraint such as $\varphi_X < 1/2$ removes the symmetry.

## Depends on

- [Gene-tree density under the multispecies coalescent with introgression](multispecies-coalescent-with-introgression-gene-tree-density.md)

## Expansion

Under $\Theta$ a lineage from $A$ goes vertically into $XR$ with probability $\varphi_X$ and there coalesces at rate $2/\theta_X$. Under $\Theta'$ the same lineage goes horizontally into $YR$ with probability $1 - \varphi'_X = \varphi_X$, and there coalesces at rate $2/\theta'_Y = 2/\theta_X$. The same holds with the roles swapped for the other branch and for lineages from $B$ at $Y$. Thus the bijection that exchanges the labels $XR \leftrightarrow YR$ (and left $\leftrightarrow$ right at both nodes) maps the lineage-routing and coalescence events of $\Theta$ onto those of $\Theta'$ with identical probabilities and rates. The populations $A$, $B$, $R$ and the times are untouched. The two parameter points describe the same relatedness of the sampled sequences. The posterior therefore has "twin towers", of equal height when the priors are symmetric. A related, more elementary unidentifiability holds whenever at most one sequence per locus is sampled below a population: its $\theta$, and the times of hybridization events whose parental populations then hold at most one lineage, do not enter the gene-tree density.

## Sources

- T. Flouri, X. Jiao, B. Rannala and Z. Yang, "A Bayesian implementation of the multispecies coalescent model with introgression for phylogenomic analysis", Molecular Biology and Evolution (2020; online 2019), Discussion ("Identifiability of MSci Models") and Materials and Methods (third simulation set, model D), <https://doi.org/10.1093/molbev/msz296>, PMCID PMC7086182.
