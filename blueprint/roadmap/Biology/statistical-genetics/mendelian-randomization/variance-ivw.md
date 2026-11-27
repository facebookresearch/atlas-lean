# Variance of the IVW estimator

Let $\iota$ be a finite set of SNPs, let $\sigma_j > 0$ for every $j$, let $\hat\beta_X \in \mathbb{R}^\iota$ be fixed with $\hat\beta_{Xj} \ne 0$ for some $j$, and let $\beta \in \mathbb{R}$. Let $\mu$ be a probability measure and let $\varepsilon_j$ ($j \in \iota$) be square-integrable real random variables with $\operatorname{Cov}(\varepsilon_i, \varepsilon_j) = 0$ for $i \ne j$ and $\operatorname{Var}(\varepsilon_j) = \sigma_j^2$. Then, with $\hat\beta_{Yj} = \beta\, \hat\beta_{Xj} + \varepsilon_j$ (Burgess, Butterworth & Thompson 2013),

$$\operatorname{Var}(\hat\beta_{\mathrm{IVW}}) = \Bigl(\sum_j w_j\Bigr)^{-1} = \Bigl(\sum_j \frac{\hat\beta_{Xj}^2}{\sigma_j^2}\Bigr)^{-1},$$

where $\hat\beta_{\mathrm{IVW}}$ is the [IVW estimator](ivw.md).

## Sources

- S. Burgess, A. Butterworth, S. G. Thompson, *Mendelian randomization analysis with multiple genetic variants using summarized data*, Genet. Epidemiol. 37 (2013), 658–665.
