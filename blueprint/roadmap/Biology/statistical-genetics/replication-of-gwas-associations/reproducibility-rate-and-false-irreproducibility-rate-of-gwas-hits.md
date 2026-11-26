# Reproducibility rate and false irreproducibility rate of GWAS hits

**Setting.** A SNP is tested in a primary study ($j = 1$) and an independent replication study ($j = 2$). In study $j$ the estimated log odds ratio $\hat\mu^{(j)}$ is approximately $\mathcal{N}(\mu, (\sigma^{(j)})^2)$, with Woolf standard error $\sigma^{(j)}$, and $z^{(j)} = \hat\mu^{(j)}/\sigma^{(j)}$. The SNP is a primary positive if $|z^{(1)}| > z_{\alpha_1/2}$, and it replicates if $\operatorname{sgn}(z^{(1)})\, z^{(2)} > z_{\alpha_2}$ (same direction, one-sided level $\alpha_2$), where $z_u$ is the upper $u$-quantile of $\mathcal{N}(0,1)$. For a primary positive define

$$RR = P\big(\operatorname{sgn}(z^{(1)}) Z^{(2)} > z_{\alpha_2} \,\big|\, z^{(1)}\big), \qquad FIR = P\big(\mathcal{H}_1 \,\big|\, \operatorname{sgn}(z^{(1)}) Z^{(2)} \le z_{\alpha_2},\ z^{(1)}\big),$$

the reproducibility rate and the false irreproducibility rate (probability that a non-replicating hit is nevertheless a true association).

**Decomposition.** With the primary local false discovery rate $fdr^{(1)} = P(\mathcal{H}_0 \mid z^{(1)})$ and the Bayesian predictive power $\eta^{(2)} = P(\operatorname{sgn}(z^{(1)}) Z^{(2)} > z_{\alpha_2} \mid z^{(1)}, \mathcal{H}_1) = \mathbb{E}[\beta^{(2)}(\mu) \mid z^{(1)}, \mathcal{H}_1]$, where $\beta^{(2)}$ is the replication power function,

$$RR = fdr^{(1)}\,\alpha_2 + \big(1 - fdr^{(1)}\big)\,\eta^{(2)}, \qquad FIR = \frac{\big(1 - fdr^{(1)}\big)\big(1 - \eta^{(2)}\big)}{1 - RR}.$$

**Closed form under a spike-and-slab prior.** If $\mu \sim \pi_0 \delta_0 + (1 - \pi_0)\,\mathcal{N}(0, \sigma_0^2)$, set $\lambda = \big(1 + (\sigma^{(1)}/\sigma_0)^2\big)^{-1}$ and $s = \sqrt{1 + (\sigma_0/\sigma^{(1)})^2}$. Then

$$fdr^{(1)} = \frac{\pi_0\,\phi(z^{(1)})}{\pi_0\,\phi(z^{(1)}) + (1 - \pi_0)\, s^{-1}\phi(z^{(1)}/s)}, \qquad \eta^{(2)} = \Phi\Big(\frac{\operatorname{sgn}(z^{(1)})\, z^* - z_{\alpha_2}}{\sigma^*}\Big),$$

with $z^* = \lambda\,\hat\mu^{(1)}/\sigma^{(2)}$ and $\sigma^* = \sqrt{1 + \lambda\,(\sigma^{(1)}/\sigma^{(2)})^2}$.

## Expansion

The decomposition is Bayes' formula: under $\mathcal{H}_0$ the replication statistic is standard normal and independent of $z^{(1)}$, so it replicates with probability $\alpha_2$; under $\mathcal{H}_1$ it replicates with the predictive power. For the closed form, under the slab $z^{(1)} \sim \mathcal{N}(0, s^2)$, whose density is $s^{-1}\phi(z/s)$ (the source prints the slab term of $fdr^{(1)}$ without the normalizing factor $s^{-1}$), and the posterior of $\mu$ given $\hat\mu^{(1)}$ is $\mathcal{N}(\lambda\hat\mu^{(1)}, \lambda(\sigma^{(1)})^2)$, so the predictive law of $\hat\mu^{(2)}$ is $\mathcal{N}\big(\lambda\hat\mu^{(1)}, \lambda(\sigma^{(1)})^2 + (\sigma^{(2)})^2\big)$. Because of the winner's curse ($\lambda < 1$ shrinks the primary estimate), $RR$ is often far below the nominal power computed at $\hat\mu^{(1)}$; $RR$ guides replication sample size, and a large $FIR$ flags non-replicated hits worth re-examining.

## Sources

- W. Jiang, J.-H. Xue and W. Yu, "Estimating Reproducibility in Genome-Wide Association Studies", arXiv:1508.06715 (2015), Section 2.1 (definitions of $RR$ and $FIR$ and their relation to $fdr$ and predictive power), Section 2.2 (two-component mixture prior, closed forms) and the appendix derivations, <https://doi.org/10.48550/arXiv.1508.06715>.
