# Number of permutations for a maxT genome-wide threshold

**Setting.** $m$ markers are tested with statistics $t_1,\dots,t_m$. For each of $q$ permutations $k$, compute the statistics ${}^k t_i$ and their maximum ${}^k t_{\max} = \max_{i} {}^k t_i$ (the Westfall-Young maxT method). The adjusted permutation p-value of marker $i$ is

$$\hat p_i = \frac1q\sum_{k=1}^q \mathbb{1}\big({}^k t_{\max} \ge t_i\big).$$

Then $\hat p_i \le \alpha$ exactly when $t_i$ exceeds the $(1-\alpha)$ quantile of the permutation maxima; equivalently, the genome-wide threshold on p-values is the $\alpha$ quantile of the per-permutation minimal p-values. This threshold controls the family-wise error rate.

**Choice of $q$.** Since $\sum_k \mathbb{1}({}^kt_{\max}\ge t_i)\sim\mathrm{Bin}(q,p_i)$, at the decision boundary $p_i = \alpha$ the standard error of $\hat p_i$ is $\sqrt{\alpha(1-\alpha)/q}$, and $\hat p_i \pm z_\gamma\,\mathrm{SE}$ is a $\gamma$ confidence interval with $z_\gamma$ the $(1+\gamma)/2$ standard normal quantile. Requiring half-width at most a precision $\theta$ gives

$$q \ \ge\ \frac{z_\gamma^2\,\alpha(1-\alpha)}{\theta^2}.$$

## Depends on

- [Population-aware permutations in linear mixed models](population-aware-permutations-in-linear-mixed-models.md)

## Expansion

The bound is the normal-approximation sample size for estimating a binomial proportion near $\alpha$ to within $\pm\theta$. For example, $\alpha = 0.05$, $\gamma = 0.95$ ($z_\gamma\approx 1.96$) and $\theta = 0.02$ give $q \ge 1.96^2\cdot 0.0475/0.0004 \approx 457$; the study used 500 permutations. The permutation threshold adapts to correlation among markers and to non-Gaussian phenotypes, which is why it is less conservative than Bonferroni for normal phenotypes and stricter for strongly skewed ones.

## Sources

- John M, Korte A, Todesco M, Grimm DG. Population-aware permutation-based significance thresholds for genome-wide association studies. *Bioinformatics Advances* 4(1):vbae168 (2024), Section 2.2, Eqs. 3-4. <https://doi.org/10.1093/bioadv/vbae168>. PMCID: PMC11639184.
