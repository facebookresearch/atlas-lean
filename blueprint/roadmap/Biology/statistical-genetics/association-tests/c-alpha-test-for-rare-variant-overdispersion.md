# C-alpha test for rare-variant overdispersion

**Setting.** A case-control study is sequenced over a target region (a gene or exon set) containing $m$ distinct rare variants. Variant $i$ is observed $n_i \ge 1$ times in total, $y_i$ of them in cases. Let $p_0 \in (0,1)$ be the probability that a copy falls in a case when the variant is unrelated to phenotype (for equal numbers of case and control chromosomes, $p_0 = 1/2$). Assume the counts of different variants are independent and

$$y_i \mid n_i \sim \operatorname{Binomial}(n_i, p_i).$$

**Hypotheses.** $H_0$: $p_i = p_0$ for all $i$. The alternative is that the $p_i$ are drawn from a mixture: some variants are risk alleles ($p_i > p_0$), some neutral ($p_i = p_0$) and some protective ($p_i < p_0$). Any such mixture inflates the variance of $y_i$ above the binomial value.

**Statistic.** Let $m(n)$ be the number of variants observed exactly $n$ times and $f(u \mid n, p_0) = \binom nu p_0^u(1-p_0)^{n-u}$. Define

$$T = \sum_{i=1}^{m}\Bigl[(y_i - n_i p_0)^2 - n_i p_0(1-p_0)\Bigr],$$

$$c = \sum_{n} m(n) \sum_{u=0}^{n}\Bigl[(u - n p_0)^2 - n p_0(1-p_0)\Bigr]^2 f(u \mid n, p_0),$$

$$Z = T/\sqrt c .$$

Under $H_0$, $\mathbb E[T] = 0$ and $\operatorname{Var}(T) = c$ exactly, and $Z$ is referred to a one-sided standard normal (or to its permutation distribution): $H_0$ is rejected for large $Z$.

**Score-test property.** Let $p_i = p_0 + \varepsilon_i$ with independent mean-zero random effects of variance $\tau$. The derivative at $\tau = 0$ of the marginal log-likelihood is proportional to

$$U = \sum_{i=1}^{m}\Bigl[(y_i - n_i p_0)^2 - n_i p_0(1-p_0) - (1 - 2p_0)(y_i - n_i p_0)\Bigr],$$

so $U$ is the score statistic for $\tau = 0$ (Neyman and Scott's $C(\alpha)$ test for binomial overdispersion). It differs from $T$ by the linear term $(1 - 2p_0)\sum_i (y_i - n_i p_0)$, so C-alpha is exactly the score test when $p_0 = 1/2$, the balanced design, and otherwise a variant of it without the linear correction.

**Singletons.** A variant with $n_i = 1$ carries no overdispersion information: its marginal law is $\mathrm{Bernoulli}(p_0)$ whatever $\tau$ is, and its summand of $U$ is identically $0$. Its summand of $T$ equals $(1-2p_0)(y_i - p_0)$, which depends only on the mean of $y_i$ and vanishes when $p_0 = 1/2$. Singletons may instead be pooled into one binomial count and entered as a single term, which is a burden test on that pool.

## Expansion

Under $H_0$ each summand of $T$ has mean $\operatorname{Var}(y_i) - n_ip_0(1-p_0) = 0$, and by independence $\operatorname{Var}(T)$ is the sum of the summands' variances, which is $c$ after grouping variants by $n$. Under a mixture alternative, $\mathbb E[(y_i - n_ip_0)^2] = n_i\,\mathbb E[p_i(1-p_i)] + n_i^2\,\mathbb E[(p_i-p_0)^2]$, and since $\mathbb E[p_i(1-p_i)] = p_0(1-p_0) - \mathbb E[(p_i-p_0)^2]$ when $\mathbb E[p_i] = p_0$, the excess is $n_i(n_i-1)\,\mathbb E[(p_i - p_0)^2] \ge 0$, strictly positive for $n_i \ge 2$. Risk and protective variants therefore add to $T$ instead of cancelling, which is the advantage over burden tests that sum counts with a common sign. For the score property, write $\ell_i(p) = y_i \log p + (n_i - y_i)\log(1 - p)$ and expand the binomial likelihood to second order in $\varepsilon_i$; integrating over $\varepsilon_i$ gives $\mathbb E[e^{\ell_i(p_0 + \varepsilon_i)}] = e^{\ell_i(p_0)}\bigl(1 + \tfrac{\tau}{2}(\ell_i'^2 + \ell_i'') + o(\tau)\bigr)$ at $p_0$. With $d_i = y_i - n_ip_0$, $\ell_i' = d_i/(p_0(1-p_0))$ and $\ell_i'' = -\bigl(n_ip_0(1-p_0) + (1-2p_0)d_i\bigr)/(p_0^2(1-p_0)^2)$, so the term linear in $\tau$ is $\tau\,[d_i^2 - n_ip_0(1-p_0) - (1-2p_0)d_i]/(2p_0^2(1-p_0)^2)$, the summand of $U$. For a doubleton with $p_0 = 1/4$ and $y_i = 0$, the summand of $T$ is $-0.125$ and that of $U$ is $+0.125$.

## Sources

- B. M. Neale, M. A. Rivas, B. F. Voight, D. Altshuler, B. Devlin, M. Orho-Melander, S. Kathiresan, S. M. Purcell, K. Roeder, M. J. Daly, *Testing for an unusual distribution of rare variants*, PLoS Genetics 7 (2011), e1001322, <https://doi.org/10.1371/journal.pgen.1001322>, PMCID PMC3048375. Methods, "C-alpha test" (statistic $T$, variance $c$, $Z = T/\sqrt c$, one-sided normal reference) and "Singleton counts"; Text S1 (derivation).
- J. Neyman, E. L. Scott, *On the use of $C(\alpha)$ optimal tests of composite hypotheses*, Bulletin of the International Statistical Institute 41 (1966), 477–497.
