# Leave-one-out corrected maximum-likelihood estimators of the local false discovery rate

**Two-groups model.** Feature $i$ (a gene, protein or metabolite) is summarized by a scalar statistic $t_i$. Its density is a mixture of a known null density $g_{\theta_0}$ and an unknown alternative $g_{\theta_{\rm alt}}$ from the same parametric family $\{g_\theta : \theta\in\Theta\}$, with null proportion $\pi_0$. The **local false discovery rate** of feature $i$ is the posterior null probability

$$\psi_i = \frac{\pi_0 g_{\theta_0}(t_i)}{\pi_0 g_{\theta_0}(t_i) + (1-\pi_0) g_{\theta_{\rm alt}}(t_i)} .$$

**Estimators.**

- **Leave-zero-out (L0O, the plain MLE):** $(\hat\theta, \hat\pi_0)$ maximize $\prod_{j=1}^N\big(\pi_0 g_{\theta_0}(t_j) + (1-\pi_0)g_\theta(t_j)\big)$, and these are plugged into $\psi_i$.
- **MDL-corrected:** for each $i$, $(\hat\theta_i, \hat\pi_{0i})$ maximize the same likelihood with the factor $j = i$ removed, and are then plugged into $\psi_i$ evaluated at $t_i$.
- **Leave-one-out (L1O):** as MDL, but $\pi_0$ is held at the L0O value and only $\theta$ is re-estimated without feature $i$.

The correction removes the dependence of the fitted prior on the statistic $t_i$ at which the densities are evaluated. With L0O, a feature with an extreme $t_i$ pulls $\hat\theta$ toward itself and makes its own LFDR too small. This negative bias is severe for the tens of features typical of proteomics or metabolomics.

**Asymptotic agreement.** Let $\theta^{\ddagger}$ minimize $\sum_{j=1}^N \min\big(-\log g_\theta(t_j), -\log g_{\theta_0}(t_j)\big)$. If each $T(X_j)$ independently has density $g_{\theta_j}$ with $\theta_j \in \{\theta_0, \theta_{\rm alt}\}$, then $\theta^{\ddagger}$, when unique, is the maximum-likelihood estimate of $\theta_{\rm alt}$ jointly over $\theta$ and the null/alternative labels. If the $X_j$ are IID under some $P_\star$, with $E_\star \log g_\theta(T(X_j)) < \infty$ for all $\theta$ and the relevant maximizers almost surely unique, then the all-feature parameter and each leave-feature-$i$-out parameter differ by a quantity that tends to $0$ almost surely as $N\to\infty$. The correction therefore matters only when the number of features is small.

## Depends on

- [Local false discovery rate](../../../../../../Probability/hypothesis-testing/two-groups-model-and-local-false-discovery-rates/local-fdr.md)

## Expansion

Replacing the min of codelengths by a max of log-likelihoods shows that $\theta^{\ddagger}$ maximizes the classification likelihood $\sup_{\boldsymbol\theta\in\{\theta_0,\theta\}^N}\prod_j g_{\theta_j}(t_j)$. The strong law of large numbers applied to the averages over $\{1,\dots,N\}$ and over $\{1,\dots,N\}\setminus\{i\}$ gives the same limiting objective, so the two argmax values converge to each other. The excluded-feature idea is inspired by minimum description length: a feature is coded with a distribution chosen without hindsight of its own data.

## Sources

- M. Padilla and D. R. Bickel, "Estimators of the local false discovery rate designed for small numbers of tests", *Statistical Applications in Genetics and Molecular Biology* 11(5) (2012), article 4, <https://doi.org/10.1515/1544-6115.1807>; preprint "Empirical Bayes methods corrected for small numbers of tests", arXiv:1009.5981 (2010), Section 3 (L0O, MDL and L1O estimators) and Appendices A–B (Theorems 1 and 3), <https://doi.org/10.48550/arXiv.1009.5981>.
