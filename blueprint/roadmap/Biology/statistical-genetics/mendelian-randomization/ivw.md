# Inverse-variance-weighted estimator

Let $\iota$ be a finite set of SNPs with SNP–exposure associations $\hat\beta_X$, SNP–outcome associations $\hat\beta_Y$ and outcome standard errors $\sigma$ in $\mathbb{R}^\iota$. The inverse-variance-weighted estimator is (Burgess, Butterworth & Thompson 2013)

$$\hat\beta_{\mathrm{IVW}} = \frac{\sum_j \hat\beta_{Xj} \hat\beta_{Yj} / \sigma_j^2}{\sum_j w_j}, \qquad w_j = \frac{\hat\beta_{Xj}^2}{\sigma_j^2},$$

with the convention $x/0 = 0$ (so it is $0$ when every $w_j$ is $0$, for instance when every $\hat\beta_{Xj} = 0$).

## Sources

- S. Burgess, A. Butterworth, S. G. Thompson, *Mendelian randomization analysis with multiple genetic variants using summarized data*, Genet. Epidemiol. 37 (2013), 658–665.
