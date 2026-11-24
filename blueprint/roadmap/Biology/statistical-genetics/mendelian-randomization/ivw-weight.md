# Inverse-variance weight of a ratio estimate

Let $\iota$ be a set of SNPs with SNP–exposure associations $\hat\beta_X \in \mathbb{R}^\iota$ and outcome standard errors $\sigma \in \mathbb{R}^\iota$. The inverse-variance weight of SNP $j$ is (Burgess, Butterworth & Thompson 2013)

$$w_j = \frac{\hat\beta_{Xj}^2}{\sigma_j^2},$$

with the convention $x/0 = 0$.

## Sources

- S. Burgess, A. Butterworth, S. G. Thompson, *Mendelian randomization analysis with multiple genetic variants using summarized data*, Genet. Epidemiol. 37 (2013), 658–665.
