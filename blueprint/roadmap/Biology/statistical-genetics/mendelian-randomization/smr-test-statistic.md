# Summary-data-based Mendelian randomization (SMR) test statistic

Let $\hat b_{zx}$ and $\hat b_{zy}$ be estimated effects of a SNP $z$ on an exposure $x$ (e.g. gene expression) and an outcome $y$, from independent samples, with $z$-statistics $z_{zx} = \hat b_{zx}/\mathrm{se}(\hat b_{zx})$ and $z_{zy} = \hat b_{zy}/\mathrm{se}(\hat b_{zy})$, $z_{zx} \ne 0$. The SMR estimate of the effect of $x$ on $y$ is the [ratio estimate](ratio-estimate.md) $\hat b_{xy} = \hat b_{zy}/\hat b_{zx}$, and its first-order (delta-method) variance is

$$\widehat{\mathrm{Var}}(\hat b_{xy}) = \hat b_{xy}^2 \Bigl(\frac{1}{z_{zy}^2} + \frac{1}{z_{zx}^2}\Bigr).$$

The SMR statistic is

$$T_{\mathrm{SMR}} = \frac{\hat b_{xy}^2}{\widehat{\mathrm{Var}}(\hat b_{xy})} = \frac{z_{zy}^2\, z_{zx}^2}{z_{zy}^2 + z_{zx}^2},$$

referred to a $\chi^2_1$ distribution under $b_{xy} = 0$ when $z_{zx}$ is large. It satisfies $T_{\mathrm{SMR}} \le \min(z_{zy}^2, z_{zx}^2)$: it is half the harmonic mean of the two squared statistics, so it is significant only if both associations are strong.

## Expansion

For $f(b_{zy}, b_{zx}) = b_{zy}/b_{zx}$ and independent estimates, the delta method gives $\mathrm{Var}(\hat b_{xy}) \approx \mathrm{Var}(\hat b_{zy})/b_{zx}^2 + b_{zy}^2 \mathrm{Var}(\hat b_{zx})/b_{zx}^4 = b_{xy}^2(1/z_{zy}^2 + 1/z_{zx}^2)$. Dividing $\hat b_{xy}^2$ by it cancels $\hat b_{xy}^2$. The bound follows from $1/T = 1/z_{zy}^2 + 1/z_{zx}^2$. The chi-squared reference ignores the non-normality of a ratio with a noisy denominator, which is why SMR is applied only to strong instruments.

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)

## Sources

- Z. Zhu, F. Zhang, H. Hu et al., "Integration of summary data from GWAS and eQTL studies predicts complex trait gene targets", *Nature Genetics* 48 (2016), 481–487, <https://doi.org/10.1038/ng.3538>. The SMR statistic, reconstructed from the published method (full text not available; no equation numbers cited).
