# Empirical Bayes identification of positively selected sites

In a site model with classes $k = 1, \dots, K$ of proportions $p_k$ and ratios $\omega_k$, the naive empirical Bayes (NEB) posterior probability that site $h$ belongs to class $k$, evaluated at the maximum-likelihood estimates, is

$$\Pr(k \mid x_h) = \frac{p_k f(x_h \mid \omega_k)}{\sum_{j=1}^{K} p_j f(x_h \mid \omega_j)},$$

and the site's posterior probability of positive selection is the sum over classes with $\omega_k > 1$. The Bayes empirical Bayes (BEB) method replaces the plug-in estimates of the $\omega$-distribution parameters by an average over a discretized prior on them, weighted by their posterior given the whole alignment, which accounts for sampling error in the estimates; it reports for each site $\Pr(\omega > 1 \mid x)$ and the posterior mean and standard deviation of $\omega$. Site identification is performed only after the likelihood ratio test has supported positive selection.

## Depends on

- [Site-model likelihood ratio tests for positive selection](site-model-likelihood-ratio-tests.md)

## Expansion

The NEB formula is Bayes' theorem with the mixture proportions as prior class probabilities. When the alignment is small, the maximum-likelihood estimate of the selected class's $\omega$ and proportion can be very unstable, and plugging it in produces overconfident site posteriors; BEB integrates this uncertainty out, which is why it should be used instead of NEB. In the worked example under M8, 14 sites had posterior probability above $0.5$ for $\omega > 1$, but posteriors such as $0.564$ with posterior mean $\omega = 1.468$ (SD $0.634$) at a single site are weak evidence, consistent with the conflicting M1a–M2a and M7–M8 test results for that gene.

## Sources

- Álvarez-Carretero S, Kapli P, Yang Z. Beginner's guide on the use of PAML to detect positive selection. *Molecular Biology and Evolution* (2023), "Detection of Adaptive Molecular Evolution Under Models of Codon Substitution", and Protocol, "Site Models With Heterogeneous ω Across Sites" and "Branch-site Model With Heterogeneous ω Across Branches and Sites". DOI <https://doi.org/10.1093/molbev/msad041>. PMCID PMC10127084.
