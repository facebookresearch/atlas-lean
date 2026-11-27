# Conditional moments of site-frequency counts under Poisson mutation

Let $G$ be the Kingman genealogy of $n$ sampled genes, with [holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md) $T_k$, and let infinite-sites mutations fall on its branches as a Poisson process of rate $\theta/2$ per unit of branch length. Let $\xi_i$ be the number of sites at which exactly $i$ genes carry the mutant type, and $L_i$ the [total length of the branches subtending exactly $i$ leaves](../expected-site-frequency-spectrum/sfs-length.md). Then, given $G$, the $\xi_i$ are independent Poisson variables with means $\frac\theta2L_i$. Hence $\xi_i$ is square integrable, $E[\xi_i \mid G] = \frac\theta2L_i$ and $E[\xi_i\xi_j \mid G] = \frac{\theta^2}4L_iL_j + \delta_{ij}\frac\theta2L_i$, that is, $\mathrm{Cov}(\xi_i, \xi_j \mid G) = \delta_{ij}\frac\theta2L_i$: the counts have the [conditional moments of the site frequency spectrum given the genealogy](sfscond-moments.md), with branch lengths $L_i$ (Birkner, Blath and Eldon 2013, Theorem S0.5, after Fu 1995). This conditional Poisson structure is the result of this page.

As consequences, with $E[L_i] = 2/i$ and $\mathrm{Cov}(L_i, L_j) = 4\sigma_{ij}$ for [Fu's covariance matrix](../fu-s-covariances-of-the-site-frequency-spectrum/fu-sigma.md) $\sigma_{ij}$, the laws of total expectation and covariance give Fu's formulas: the [expected site frequency spectrum](../expected-site-frequency-spectrum/integral-sfs.md) $E[\xi_i] = \theta/i$ and [Fu's covariance of the site frequency spectrum](../fu-s-branch-length-covariances-for-every-sample/covariance-count-kingman-eq-fu-sigma.md) $\mathrm{Cov}(\xi_i, \xi_j) = \delta_{ij}\theta/i + \theta^2\sigma_{ij}$, which are stated and proved on those pages.

## Depends on

- [Conditional moments of the site frequency spectrum given the genealogy](sfscond-moments.md)
- [Total branch length subtending $i$ sample copies](../expected-site-frequency-spectrum/sfs-length.md)
- [Fu's covariance matrix $\sigma_{ij}$](../fu-s-covariances-of-the-site-frequency-spectrum/fu-sigma.md)
- [Holding times of Kingman's coalescent](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)

## Proof depends on

- [Expected block counts weighted by coalescence times sum to $2/i$](../../../Biology/coalescent-theory/expected-site-frequency-spectrum/sum-block-count-mul-inv-choose-two.md)
- [Fu's branch-length covariances under Kingman's coalescent](../../../Biology/coalescent-theory/fu-s-branch-length-covariances-for-every-sample/covariance-sfs-length-eq-four-mul-fu-sig.md)

## Expansion

1. The Poisson marking of the branches given the genealogy, and the restriction of a Poisson process to the disjoint sets of branches subtending $i$ leaves, which gives independent Poisson counts.
2. The conditional means and covariances.
3. The laws of total expectation and covariance: $\mathrm{Cov}(\xi_i, \xi_j) = E[\mathrm{Cov}(\xi_i, \xi_j \mid G)] + \mathrm{Cov}(\frac\theta2L_i, \frac\theta2L_j)$.
4. The inputs: the [expected block counts weighted by coalescence times](../../../Biology/coalescent-theory/expected-site-frequency-spectrum/sum-block-count-mul-inv-choose-two.md), which give $E[L_i] = 2/i$, and [Fu's branch-length covariances under Kingman's coalescent](../../../Biology/coalescent-theory/fu-s-branch-length-covariances-for-every-sample/covariance-sfs-length-eq-four-mul-fu-sig.md), and the resulting [Fu covariance of the site frequency spectrum](../../../Biology/coalescent-theory/fu-s-branch-length-covariances-for-every-sample/covariance-count-kingman-eq-fu-sigma.md), whose conditional-moment hypothesis this node discharges (compare [conditional SFS moments under Kingman's coalescent](sfs-cond-moments-kingman.md)); the [expected site frequency spectrum](../../../Biology/coalescent-theory/expected-site-frequency-spectrum/integral-sfs.md) $E\xi_i = \theta/i$ is a consumer of the same inputs.

## Sources

- M. Birkner, J. Blath and B. Eldon, Statistical properties of the site-frequency spectrum associated with Λ-coalescents, Genetics 195 (2013), 1037–1053. <https://arxiv.org/abs/1305.6043>
- Original result: Y.-X. Fu, Statistical properties of segregating sites, Theor. Popul. Biol. 48 (1995), 172–197. <https://doi.org/10.1006/tpbi.1995.1025> The formulas follow Birkner, Blath and Eldon (2013), Theorem S0.5.
