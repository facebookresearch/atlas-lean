# Cross-tissue heritability by Kronecker-structured variance components

Measure the expression of gene $g$ in two tissues, $b$ and $a$, in the same $N$ individuals, each standardized to mean $0$ and variance $1$, and stack them as $(e_{bg}, e_{ag}) \in \mathbb{R}^{2N}$. With the local-IBD matrix $\Gamma_g$ and genome-wide IBD matrix $\Theta$ of the [cis–trans model](cis-trans-heritability-from-local-and-genome-wide-ibd.md), model $(e_{bg}, e_{ag}) \sim \mathcal{N}(0, W_g)$ with

$$W_g = \begin{pmatrix} h_{bg,\mathrm{cis}}^2 & \xi_{g,\mathrm{cis}}^2 \\ \xi_{g,\mathrm{cis}}^2 & h_{ag,\mathrm{cis}}^2 \end{pmatrix} \otimes \Gamma_g + \begin{pmatrix} h_{bg,\mathrm{trans}}^2 & \xi_{g,\mathrm{trans}}^2 \\ \xi_{g,\mathrm{trans}}^2 & h_{ag,\mathrm{trans}}^2 \end{pmatrix} \otimes \Theta + \begin{pmatrix} 1 - h_{bg}^2 & \rho_g - \xi_g^2 \\ \rho_g - \xi_g^2 & 1 - h_{ag}^2 \end{pmatrix} \otimes I_N,$$

where $\otimes$ is the Kronecker product of a $2 \times 2$ matrix with an $N \times N$ matrix, $h_{\cdot g}^2 = h_{\cdot g,\mathrm{cis}}^2 + h_{\cdot g,\mathrm{trans}}^2$ are the single-tissue heritabilities, $\rho_g$ is the cross-tissue correlation of expression within an individual, and $\xi_g^2 = \xi_{g,\mathrm{cis}}^2 + \xi_{g,\mathrm{trans}}^2$ is the **cross-tissue heritability**, the part of the cross-tissue covariance carried by inherited variation. The upper-left $N \times N$ block of the first term has entries $h_{bg,\mathrm{cis}}^2 \gamma_{g,st}$ and the upper-right block entries $\xi_{g,\mathrm{cis}}^2 \gamma_{g,st}$. All parameters are fitted by maximum likelihood, and the ratio $\xi_{\mathrm{cis}}^2 / \xi^2$ (averaged over genes) measures how much of the heritability shared between tissues is due to cis regulation.

## Depends on

- [Cis and trans heritability from local and genome-wide IBD](cis-trans-heritability-from-local-and-genome-wide-ibd.md)

## Expansion

For individuals $s \ne t$, the covariance of tissue-$b$ expression in $s$ with tissue-$a$ expression in $t$ is $\xi_{g,\mathrm{cis}}^2 \gamma_{g,st} + \xi_{g,\mathrm{trans}}^2 \theta_{st}$: only the genetic values are shared between relatives, and the same allele can act in both tissues. Within an individual ($s = t$, where $\gamma_{g,ss} = \theta_{ss} = 1$) the cross-tissue covariance is $\xi_g^2 + (\rho_g - \xi_g^2) = \rho_g$, so the environmental (non-shared) part is $\rho_g - \xi_g^2$. This is the bivariate (cross-phenotype) generalization of the variance-components model, previously used for two measurements of height. Since $\Gamma_g$, $\Theta$ and $I_N$ are positive semidefinite, positive semidefiniteness of each $2 \times 2$ factor (e.g. $\xi_{g,\mathrm{cis}}^4 \le h_{bg,\mathrm{cis}}^2 h_{ag,\mathrm{cis}}^2$) suffices for $W_g$ to be a valid covariance matrix. Applied to blood and adipose tissue in Icelandic families, the cross-tissue correlation was mostly explained by cis heritability, with little sharing of trans effects; standard errors of $\rho_g$ come from the jackknife over individuals.

## Sources

- A. L. Price, A. Helgason, G. Thorleifsson, S. A. McCarroll, A. Kong and K. Stefansson, "Single-tissue and cross-tissue heritability of gene expression via identity-by-descent in related or unrelated individuals", PLoS Genetics (2011), e1001317, Methods "Cross-tissue analysis" and Results "Cross-tissue analysis", <https://doi.org/10.1371/journal.pgen.1001317>, PMCID PMC3044684.
