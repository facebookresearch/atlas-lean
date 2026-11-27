# Heterogeneity in single-hit dose–response models

**Model.** In a single-hit dose–response model, a host ingesting a dose of $n$ microbes becomes infected if at least one microbe independently succeeds, microbe $i$ succeeding with probability (infectivity) $x_i \in [0, 1]$. The probability of infection is

$$P_h = 1 - \prod_{i=1}^n (1 - x_i),$$

with mean infectivity $\bar x$ and central moments $M_k = n^{-1}\sum_i (x_i - \bar x)^k$. If moreover $\bar x < 1$ and $|x_i - \bar x| < 1 - \bar x$ for every $i$, expanding $\ln(1 - z_i)$ with $z_i = (x_i - \bar x)/(1 - \bar x)$ gives

$$P_h = 1 - (1 - \bar x)^n \exp\Big(-n\sum_{k \ge 1}\frac{M_k}{k(1 - \bar x)^k}\Big);$$

without this condition the series may diverge (for $x = (0, 0.99, 0.99)$, $z_1 \approx -1.94$). With homogeneous dose and infectivity (model $A$), $P^{(A)}(x, n) = 1 - (1 - x)^n$. Between-host heterogeneity is modeled by a random infectivity $x$ on $[0,1]$ with mean $\mu_x$ and variance $v_x$ (e.g. $x \sim \mathrm{Beta}(\alpha, \beta)$) and a random dose $n \in \mathbb{Z}^+$ with mean $\mu_n$ and variance $v_n$ (Poisson: models $A'_1$, $C'_1$; negative binomial with $v_n > \mu_n$: models $A'_2$, $C'_2$; $C_1$ has random infectivity and fixed dose). Let $\hat P$ be the expected probability of infection across hosts.

**Theorem.**

1. *(Within-host heterogeneity raises risk.)* For a host ingesting $n$ microbes with mean infectivity $\bar x$, the probability of infection is minimal when all microbes have the same infectivity $x_i = \bar x$.
2. *(Between-host heterogeneity lowers average risk.)* If $\hat P$ is computed from $P^{(A)}$ with independent random infectivity and dose as above, then in the limit of small infectivity $\hat P$ is decreasing in both $v_x$ and $v_n$; and the slope of $\hat P$ at the median dose $\mu_{50}$ (where $\hat P = 1/2$) increases with $\mu_x$ and decreases with $v_x$, for any dose distribution.
3. *(Ordering of standard models.)* For a fixed mean dose, the expected infection probability of the negative-binomial-dose models decreases with the dose variance, and they reduce to the Poisson-dose models as $v_n \searrow \mu_n$. For all parameters,

    $$P^{(A)}(x, \mu_n) \ge P^{(A'_1)}(x, \mu_n) \ge P^{(A'_2)}(x, \mu_n, v_n),$$

    $$P^{(A)}(\mu_x, \mu_n) \ge P^{(C_1)}(\mu_x, v_x, \mu_n) \ge P^{(C'_1)}(\mu_x, v_x, \mu_n) \ge P^{(C'_2)}(\mu_x, v_x, \mu_n, v_n).$$

## Proof depends on

- [Jensen's inequality](../../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md)

## Expansion

Within a host, $\log(1 - P_h) = \sum_i \log(1 - x_i)$ is a sum of concave functions, so by Jensen's inequality spreading infectivities at fixed mean can only lower the escape probability, i.e. raise infection risk. Across hosts the relevant function is $P^{(A)}(x, n) = 1 - (1-x)^n$, which is concave in $x$ and in $n$, so averaging over heterogeneous hosts lowers the mean infection probability and flattens the dose–response curve. Ignoring heterogeneity thus biases risk assessments in opposite directions depending on whether variability lies within or between hosts, which matters when fitting exponential or beta-Poisson dose–response curves to outbreak data.

## Sources

- Francisco J. Perez-Reche, "Impact of heterogeneity on infection probability: Insights from single-hit dose–response models", Mathematical Biosciences 385 (2025), 109447, <https://doi.org/10.1016/j.mbs.2025.109447>; numbering as in arXiv:2404.00822: Lemma 2.1, Theorem 2.2, Theorem 4.1, Corollary 4.1.1, Propositions 4.1–4.5 and Corollaries 4.2.1–4.2.2.
