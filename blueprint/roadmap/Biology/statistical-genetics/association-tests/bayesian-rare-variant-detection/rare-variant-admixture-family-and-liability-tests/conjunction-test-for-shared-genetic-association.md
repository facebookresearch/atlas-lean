# Conjunction test for shared genetic association

For one SNP tested for association with two traits, let $p_1, p_2$ be the two p-values and consider the **conjunction null** $H_0 = H_{01} \cup H_{02}$ (at least one trait is not associated), whose rejection asserts that the SNP is associated with both traits. The conjunction p-value

$$P_{\mathrm{conj}} = \max(p_1, p_2)$$

gives a valid level-$\alpha$ test: if each $p_i$ is super-uniform under its own null ($P(p_i \le \alpha) \le \alpha$ when $H_{0i}$ holds), then $P(P_{\mathrm{conj}} \le \alpha) \le \alpha$ under every configuration in $H_0$, with no assumption on the dependence between $p_1$ and $p_2$. Because it must be calibrated for the worst configuration in the composite null (one null true, the other alternative arbitrarily strong), it is conservative when both nulls hold.

A less conservative variant uses the estimated fraction of false nulls among $n$ tests of trait $i$, from Storey's estimator at tuning parameter $\lambda \in [0,1)$:

$$\hat\pi_i(\lambda) = 1 - \frac{\#\{j : p_i^{(j)} > \lambda\}}{(1 - \lambda)\, n}.$$

If null p-values are uniform, $E[\hat\pi_i(\lambda)] \le \pi_i$, the true fraction of non-null tests, so the estimate is conservative.

## Expansion

Validity: under $H_0$ some $H_{0i}$ holds, and $\{\max(p_1,p_2) \le \alpha\} \subseteq \{p_i \le \alpha\}$, so $P(P_{\mathrm{conj}} \le \alpha) \le P(p_i \le \alpha) \le \alpha$. When both nulls hold and the p-values are independent and uniform, $P(P_{\mathrm{conj}} \le \alpha) = \alpha^2$, which is the source of the conservativeness. For Storey's estimator, $E[\#\{p > \lambda\}] = (1-\pi_i)n(1-\lambda) + \sum_{\text{non-null } j} P(p^{(j)} > \lambda) \ge (1 - \pi_i)n(1-\lambda)$, giving $E[\hat\pi_i(\lambda)] \le \pi_i$; Storey posed $\#\{p > \lambda\}/((1-\lambda)n)$ as an estimate of the proportion of true nulls, and Franke et al. point out that an earlier relaxed conjunction method inverted this expression incorrectly, giving the corrected form above, used with $\lambda = 0.25$. Conjunction inference differs from meta-analysis, which rejects when at least one null is false.

## Sources

- B. Franke, J. L. Stein, S. Ripke, V. Anttila, D. P. Hibar, K. J. E. van Hulzen, A. Arias-Vasquez, J. W. Smoller, T. E. Nichols, M. C. Neale et al., "Genetic influences on schizophrenia and subcortical brain volumes: large-scale proof of concept", Nature Neuroscience 19 (2016), Online Methods ("Conjunction analysis"), <https://doi.org/10.1038/nn.4228>, PMCID: PMC4852730.
- J. D. Storey, "A direct approach to false discovery rates", Journal of the Royal Statistical Society Series B 64 (2002), 479–498, <https://doi.org/10.1111/1467-9868.00346>.
