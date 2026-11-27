# Branch-site model A test of positive selection on foreground lineages

Partition the branches of the tree, before seeing the data, into foreground branches (tested for positive selection) and background branches. Branch-site model A has four site classes with proportions

$$p_0, \quad p_1, \quad p_{2a} = (1 - p_0 - p_1)\frac{p_0}{p_0 + p_1}, \quad p_{2b} = (1 - p_0 - p_1)\frac{p_1}{p_0 + p_1},$$

in which class 0 has $0 < \omega_0 < 1$ on all branches, class 1 has $\omega_1 = 1$ on all branches, and classes 2a and 2b have $\omega_0$ and $\omega_1 = 1$ respectively on the background but $\omega_2 \ge 1$ on the foreground. The null model fixes $\omega_2 = 1$. Under the null, the statistic $2\Delta\ell$ is asymptotically distributed as the $50{:}50$ mixture of a point mass at $0$ and $\chi^2_1$, so the $5\%$ critical value is $2.71$ (the $\chi^2_1$ critical value $3.84$ gives a conservative test). Sites with high posterior probability of classes 2a or 2b are candidates for positive selection along the foreground lineages.

## Depends on

- [Site-model likelihood ratio tests for positive selection](site-model-likelihood-ratio-tests.md)

## Expansion

The null value $\omega_2 = 1$ lies on the boundary of the alternative's parameter space $\omega_2 \ge 1$, so with probability one half the unconstrained estimate sits on the boundary and the statistic is zero; this gives the mixture null. Fixing $\omega_1 = 1$ rather than estimating it, and allowing $0 < \omega_0 < 1$ rather than $\omega_0 = 0$, is what distinguishes the modified model A from the older models A and B, which produced false positives when weakly constrained sites were absorbed into the selected class. A test with $\omega_2 = 1$ as null discriminates positive selection from relaxed constraint on the foreground, which a test against M1a cannot. Testing many branches without a prior hypothesis requires multiple-testing correction, for which Rom's procedure or false-discovery-rate control is preferred to Bonferroni.

## Sources

- Álvarez-Carretero S, Kapli P, Yang Z. Beginner's guide on the use of PAML to detect positive selection. *Molecular Biology and Evolution* (2023), "Detection of Adaptive Molecular Evolution Under Models of Codon Substitution", and Protocol, "Site Models With Heterogeneous ω Across Sites" and "Branch-site Model With Heterogeneous ω Across Branches and Sites". DOI <https://doi.org/10.1093/molbev/msad041>. PMCID PMC10127084.
