# Distribution of traced contacts per index case

**Setting.** Use the tree epidemic with contact tracing of the companion article: downstream degree $K$, infection rate $\beta$ per edge, unobserved recovery rate $\alpha$, diagnosis rate $\sigma$, tracing probability $p$ per edge, one-step tracing. Index cases have age-at-diagnosis density $\varphi(a)$ and each downstream contact is traced with probability $\hat p(a)$. Let $I_a$ indicate that the index case's infector is still infectious when the index case is diagnosed at age $a$; to leading order in $p$, $P(I_a = 1) = e^{-(\alpha+\sigma)a}$.

**Proposition (forward tracing, fixed degree).** If $K \equiv k$, the number $T$ of individuals traced forward by one index case has

$$P(T = i) = \int_0^\infty \binom{k}{i}\hat p(a)^i\big(1 - \hat p(a)\big)^{k-i}\,\beta(k-1)\, e^{-\beta(k-1)a}\, da, \qquad i = 0, \dots, k.$$

**Proposition (full tracing).** With forward and backward tracing, the total number $T_{\mathrm{tot}}$ of traced individuals per index case has

$$P(T_{\mathrm{tot}} = i) = \int_0^\infty \Big[p\,P(I_a = 1)\,P(T = i-1 \mid a) + \big(1 - p\,P(I_a = 1)\big)P(T = i \mid a)\Big]\varphi(a)\, da,$$

with $P(T = i \mid a) = \binom{k}{i}\hat p(a)^i(1-\hat p(a))^{k-i}$ for $0 \le i \le k$ and $P(T = i \mid a) = 0$ otherwise. For a random degree, write $P_k(T = j \mid a)$ for this binomial probability with degree $k$; then

$$P(T_{\mathrm{tot}} = i) = \sum_{k \ge \max(i-1,0)} P(K = k)\int_0^\infty \Big[p\,P(I_a = 1)\,P_k(T = i-1 \mid a) + \big(1 - p\,P(I_a = 1)\big)P_k(T = i \mid a)\Big]\varphi(a)\, da,$$

where the term $k = i-1$ contributes only through backward tracing, so that the probabilities sum to $1$ over $i \ge 0$.

**Corollary (identifiability).** After rescaling age by $\beta$, $P(T = i)$ and $P(T_{\mathrm{tot}} = i)$ depend on $(\alpha, \beta, \sigma)$ only through $R_0 = \mathbb E[K]\beta/(\alpha+\sigma+\beta)$, besides the degree distribution and $p$. Counts of traced contacts per index case therefore identify $R_0$ and $p$ by maximum likelihood, but not the individual rates.

## Depends on

- [Age at diagnosis and per-contact tracing probability on a random tree](age-at-diagnosis-and-per-contact-tracing-probability-on-a-random-tree.md)

## Proof sketch

Given the age $a$ at diagnosis, the $k$ downstream edges are traced independently, each with probability $\hat p(a)$, so $T \mid a \sim \mathrm{Binomial}(k, \hat p(a))$. Integrating against $\varphi$ with $\mathbb E[K] = k$ gives the first formula. Backward tracing adds the infector exactly when it is still infectious ($I_a = 1$) and its edge is traced (probability $p$), which shifts the count by one; conditioning on $I_a$ gives the mixture. For the corollary, substitute $a = b/\beta$. Then $\hat p$, $\varphi(a)\,da$ and $P(I_a = 1)$ depend on the rates only through $r = (\alpha+\sigma)/\beta$, and $r = \mathbb E[K]/R_0 - 1$.

## Sources

- Augustine Okolie, Johannes Müller and Mirjam Kretzschmar, "Parameter estimation for contact tracing in graph-based models", *Journal of The Royal Society Interface* 20 (2023), 20230409, <https://doi.org/10.1098/rsif.2023.0409>. Preprint version: arXiv:2307.08370 (2023), Propositions 4.2 and 4.3, Section 4.2, Corollary 4.4 and Section 5, <https://doi.org/10.48550/arXiv.2307.08370>.
