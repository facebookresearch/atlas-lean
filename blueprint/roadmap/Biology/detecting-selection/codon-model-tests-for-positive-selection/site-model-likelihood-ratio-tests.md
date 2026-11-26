# Site-model likelihood ratio tests for positive selection

Let $x_h$ be the data at codon site $h$ of an alignment on a fixed tree, and $f(x_h \mid \omega)$ its likelihood under a reversible codon substitution model with nonsynonymous/synonymous rate ratio $\omega$, computed by the pruning algorithm. A site model treats $\omega$ at each site as drawn from a distribution with $K$ classes,

$$f(x_h) = \sum_{k=1}^{K} p_k\, f(x_h \mid \omega_k), \qquad \ell = \sum_h \log f(x_h),$$

with the nested pairs

- **M1a (nearly neutral)**: $p_0$ with $0 < \omega_0 < 1$, $p_1 = 1 - p_0$ with $\omega_1 = 1$ (2 free parameters), against **M2a (positive selection)**, which adds a class $p_2$ with $\omega_2 > 1$ (4 free parameters);
- **M7 (beta)**: $\omega \sim \mathrm{Beta}(p, q)$ on $(0, 1)$, discretized (2 parameters), against **M8 (beta & ω)**: a proportion $p_0$ from the beta and $p_1 = 1 - p_0$ with $\omega_s > 1$ (4 parameters).

Positive selection on some sites is inferred when $2\Delta\ell = 2(\ell_1 - \ell_0)$ exceeds the $\chi^2_2$ critical value, $5.99$ at the $5\%$ level and $9.21$ at the $1\%$ level. The comparison of the one-ratio model M0 with M1a tests variation of $\omega$ among sites, not positive selection.

## Depends on

- [Goldman–Yang codon rate matrix](../../phylogenetics/codon-substitution-models-and-dn-ds/gy-rate.md)
- [Site likelihood of a phylogenetic tree](../../phylogenetics/felsenstein-s-pruning-algorithm/likelihood.md)

## Expansion

The $\omega$ ratio averaged over all sites and lineages rarely exceeds one even for genes with adaptive sites, because most codons are under purifying selection; allowing a class of sites with $\omega > 1$ concentrates the signal. The degrees of freedom equal the difference in free parameters (2 for both pairs), and the $\chi^2$ reference is conservative for M1a–M2a because $\omega_2 > 1$ and $p_2 \ge 0$ sit on a boundary under the null. In the worked example of a 12-sequence vertebrate gene, M1a fitted far better than M0 ($2\Delta\ell = 559.26$), M2a gave no improvement over M1a ($2\Delta\ell = 0$), but M8 beat M7 ($2\Delta\ell = 12.54 > 5.99$); when the evidence is weak the M1a–M2a test is the more stringent, because weakly selected sites tend to be absorbed into the class with $\omega_1 = 1$. All site models share the branch lengths, transition/transversion ratio and codon frequencies, so differences in $\ell$ come only from the $\omega$ distribution.

## Sources

- Álvarez-Carretero S, Kapli P, Yang Z. Beginner's guide on the use of PAML to detect positive selection. *Molecular Biology and Evolution* (2023), "Detection of Adaptive Molecular Evolution Under Models of Codon Substitution", and Protocol, "Site Models With Heterogeneous ω Across Sites" and "Branch-site Model With Heterogeneous ω Across Branches and Sites". DOI <https://doi.org/10.1093/molbev/msad041>. PMCID PMC10127084.
