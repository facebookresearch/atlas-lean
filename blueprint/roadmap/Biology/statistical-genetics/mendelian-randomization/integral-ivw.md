# Unbiasedness of the IVW estimator

Let $\iota$ be a finite set of SNPs, let $\sigma_j > 0$ for every $j$, let $\hat\beta_X \in \mathbb{R}^\iota$ be fixed with $\hat\beta_{Xj} \ne 0$ for some $j$, and let $\beta \in \mathbb{R}$. Let $\mu$ be a probability measure and let $\varepsilon_j$ ($j \in \iota$) be $\mu$-integrable real random variables with $\int \varepsilon_j \, d\mu = 0$. Then, with $\hat\beta_{Yj} = \beta\, \hat\beta_{Xj} + \varepsilon_j$ (Burgess, Butterworth & Thompson 2013),

$$\int \hat\beta_{\mathrm{IVW}} \, d\mu = \beta,$$

where $\hat\beta_{\mathrm{IVW}}$ is the [IVW estimator](ivw.md) of $(\hat\beta_X, \hat\beta_Y, \sigma)$.

## Sources

- S. Burgess, A. Butterworth, S. G. Thompson, *Mendelian randomization analysis with multiple genetic variants using summarized data*, Genet. Epidemiol. 37 (2013), 658–665.
