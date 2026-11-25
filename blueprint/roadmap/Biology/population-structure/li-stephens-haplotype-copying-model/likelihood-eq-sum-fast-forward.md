# The likelihood of the target haplotype

Let $R$ be a field, $\rho, \varepsilon \in R$ and $y$ a sequence of [site observations](obs.md). Then for every site $t$, the likelihood of the [Li–Stephens model](hmm.md) up to site $t$ is $\sum_{k=1}^{K} \hat\alpha_t(k)$, the sum of the [collapsed forward variables](fast-forward.md).
