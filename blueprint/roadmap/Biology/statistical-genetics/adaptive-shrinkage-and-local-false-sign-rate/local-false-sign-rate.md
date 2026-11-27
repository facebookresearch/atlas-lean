# Local false discovery rate and local false sign rate

In the [adaptive shrinkage model](adaptive-shrinkage-unimodal-mixture-model.md) with fitted $\hat\pi$, define for each effect $j$ the **local false discovery rate**

$$\mathrm{lfdr}_j = \Pr(\beta_j = 0 \mid \hat\beta, \hat s, \hat\pi),$$

and the **local false sign rate**

$$\mathrm{lfsr}_j = \min\big[\Pr(\beta_j \ge 0 \mid \hat\beta, \hat s, \hat\pi),\ \Pr(\beta_j \le 0 \mid \hat\beta, \hat s, \hat\pi)\big],$$

the posterior probability of getting the sign of $\beta_j$ wrong if forced to declare it positive or negative. Then

$$\mathrm{lfdr}_j \le \mathrm{lfsr}_j \le \tfrac12 + \tfrac12\,\mathrm{lfdr}_j .$$

For a set $\Gamma \subseteq \{1, \dots, J\}$ of effects whose signs are declared, $\frac{1}{|\Gamma|}\sum_{j\in\Gamma}\mathrm{lfsr}_j$ estimates the proportion of sign errors among them, the analogue of the false discovery rate.

## Depends on

- [Adaptive shrinkage model with a unimodal mixture prior](adaptive-shrinkage-unimodal-mixture-model.md)

## Expansion

Both events $\{\beta_j \ge 0\}$ and $\{\beta_j \le 0\}$ contain $\{\beta_j = 0\}$, giving the lower bound. Their probabilities sum to $1 + \mathrm{lfdr}_j$, so the smaller is at most $(1 + \mathrm{lfdr}_j)/2$. For example, posterior probabilities $0.95$, $0.03$, $0.02$ for $\beta_j < 0$, $= 0$, $> 0$ give $\mathrm{lfdr}_j = 0.03$ and $\mathrm{lfsr}_j = \min(0.05, 0.98) = 0.05$. The paper argues that lfsr is more robust than lfdr to the poorly identified null proportion $\pi_0$, since the data constrain the sign of an effect better than whether it is exactly zero.

## Sources

- M. Stephens, "False discovery rates: a new deal", Biostatistics 18 (2017), 275–294, <https://doi.org/10.1093/biostatistics/kxw041> (PMC5379932). Section 2, Equations (2.1)–(2.8).
