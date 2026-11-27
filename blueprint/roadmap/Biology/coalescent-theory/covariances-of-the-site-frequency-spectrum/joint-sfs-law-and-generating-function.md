# Joint law and generating function of the site-frequency spectrum

Under the Kingman coalescent with $n$ lineages and infinite-sites mutation, mutations arise as independent Poisson processes of rate $\theta/2$ on the branches of the genealogy (Tavaré 2004, Sec. 3). Hence, conditionally on the genealogy, the components $\xi_1, \dots, \xi_{n-1}$ of the site-frequency spectrum are independent Poisson variables with means $\frac\theta2 L_i$, where $L_i$ is the total length of branches subtending $i$ sample copies, and their joint probability generating function is $E\bigl[\prod_i z_i^{\xi_i}\bigr] = E\bigl[\exp\bigl(\frac\theta2\sum_i (z_i - 1)L_i\bigr)\bigr]$ for $z_i \in [0, 1]$. In particular $\mathrm{Cov}(\xi_i, \xi_j) = \frac{\theta^2}{4}\mathrm{Cov}(L_i, L_j)$ for $i \ne j$, so the components are dependent although they are conditionally independent. The first and second moments are Fu's formulas (as stated in Birkner, Blath and Eldon 2013, Theorem S0.5). A recursion or closed expression for the joint law itself is not stated on this page; it is a separate target, listed in the Expansion.

## Depends on

- [Conditional moments of site-frequency counts under Poisson mutation](conditional-moments-of-site-frequency-counts.md)

## Expansion

1. The marked genealogy and the conditional Poisson structure of the spectrum.
2. The joint generating function as a functional of $(L_1, \dots, L_{n-1})$.
3. A recursion over the coalescent events for the joint law, or for the joint moment generating function of $(L_i)$.
4. The first two moments as checks: $E\xi_i = \theta/i$ and Fu's covariances.
5. An explicit pair $i \ne j$ with $\mathrm{Cov}(L_i, L_j) \ne 0$.

## Sources

- S. Tavaré, Ancestral inference in population genetics, in *Lectures on Probability Theory and Statistics*, Lecture Notes in Math. 1837, Springer, 2004, 1–188.
- Original result: Y.-X. Fu, Statistical properties of segregating sites, Theor. Popul. Biol. 48 (1995), 172–197. <https://doi.org/10.1006/tpbi.1995.1025> The moment formulas follow Birkner, Blath and Eldon (2013), Theorem S0.5.
- M. Birkner, J. Blath and B. Eldon, Statistical properties of the site-frequency spectrum associated with Λ-coalescents, Genetics 195 (2013), 1037–1053. <https://doi.org/10.1534/genetics.113.156612>
