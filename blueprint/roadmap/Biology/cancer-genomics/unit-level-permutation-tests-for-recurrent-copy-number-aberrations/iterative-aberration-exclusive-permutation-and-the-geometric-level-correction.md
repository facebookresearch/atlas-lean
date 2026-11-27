# Iterative aberration-exclusive permutation and the geometric level correction

Recurrent aberrations present in the data inflate a permutation null and cost power. The iterative scheme runs the [max-statistic permutation test](max-statistic-permutation-p-value-for-cna-units.md), masks to zero the units of every newly detected significant aberration, recomputes the permutation null on the masked matrix, and repeats until an iteration detects nothing new. Each iteration uses significance level $\alpha'$.

Suppose that, under the null distribution reached at convergence, a new detection at iteration $r$ can occur only if iterations $1,\dots,r-1$ all detected, and occurs with conditional probability $\alpha'$ given those detections. Then a false detection at iteration $r$ has probability $\alpha'^{\,r}$, and the expected number of iterations with a false detection is

$$\sum_{r=1}^{\infty} \alpha'^{\,r} = \frac{\alpha'}{1-\alpha'}, \qquad 0 < \alpha' < 1 .$$

Setting this equal to the target false-positive rate $\alpha$ gives the per-iteration level

$$\alpha' = \frac{\alpha}{1+\alpha},$$

so for $\alpha = 0.05$ the scheme tests at $\alpha' \approx 0.0476$.

## Depends on

- [Max-statistic permutation p-value for copy-number aberration units](max-statistic-permutation-p-value-for-cna-units.md)

## Expansion

Because detection at iteration $r$ implies detection at every earlier iteration, the chain rule gives $\Pr(\text{detect at } r) = \prod_{s=1}^{r} \Pr(\text{detect at } s \mid \text{detect at } s-1) = \alpha'^{\,r}$. Summing the geometric series and solving $\alpha'/(1-\alpha') = \alpha$ for $\alpha'$ yields the correction. In simulations without recurrent aberrations the authors observe an empirical family-wise error close to the nominal $0.05$.

## Sources

- X. Yuan, G. Yu, X. Hou, I.-M. Shih, R. Clarke, J. Zhang, E. P. Hoffman, R. R. Wang, Z. Zhang and Y. Wang, "Genome-wide identification of significant aberrations in cancer genome", BMC Genomics 13 (2012), 342, <https://doi.org/10.1186/1471-2164-13-342>, PMCID PMC3428679. Algorithm 2, Theorem 1 and its proof in Appendix A (Eqs. (5)–(10)).
