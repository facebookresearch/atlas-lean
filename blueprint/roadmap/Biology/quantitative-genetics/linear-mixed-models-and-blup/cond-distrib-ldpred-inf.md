# The LDpred-inf posterior

Let $M, N$ be positive natural numbers, $h^2 > 0$, and $R$ a positive definite real $M \times M$ matrix. Let $P$ be a probability measure and $\beta, \varepsilon : \Omega \to \mathbb{R}^M$ measurable and independent under $P$, with $\beta \sim N(0, \frac{h^2}{M} \mathrm{I})$ and $\varepsilon \sim N(0, \frac{1}{N} R)$, and put $\hat\beta = R\beta + \varepsilon$. Then for almost every value $\hat\beta$, the conditional distribution of $\beta$ given $\hat\beta$ is

$$N\Bigl(\bigl(R + \tfrac{M}{N h^2} \mathrm{I}\bigr)^{-1} \hat\beta,\ \tfrac{1}{N} \bigl(R + \tfrac{M}{N h^2} \mathrm{I}\bigr)^{-1}\Bigr).$$

In particular the posterior mean is the LDpred-inf estimator $(R + \frac{M}{N h^2} \mathrm{I})^{-1} \hat\beta$ (Vilhjálmsson et al. 2015; Zhu and Stephens 2017).

## Sources

- B. J. Vilhjálmsson, J. Yang, H. K. Finucane, et al., *Modeling linkage disequilibrium increases accuracy of polygenic risk scores*, Am. J. Hum. Genet. 97 (2015), 576–592.
- X. Zhu, M. Stephens, *Bayesian large-scale multiple regression with summary statistics from genome-wide association studies*, Ann. Appl. Stat. 11 (2017), 1561–1592.
