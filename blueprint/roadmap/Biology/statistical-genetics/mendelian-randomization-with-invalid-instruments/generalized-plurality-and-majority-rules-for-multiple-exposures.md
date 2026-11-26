# Generalized plurality and majority rules for multiple exposures

**Model.** For i.i.d. individuals observe an outcome $Y$, exposures (treatments) $D \in \mathbb{R}^{p_d}$, instruments $Z \in \mathbb{R}^{p_z}$ (in Mendelian randomization, genetic variants) and covariates $X$, with $p_z \ge p_d$ and

$$Y = D^{\mathsf T}\beta^* + Z^{\mathsf T}\pi^* + X^{\mathsf T}\varphi^* + u, \qquad D^{\mathsf T} = Z^{\mathsf T}\Upsilon^* + X^{\mathsf T}\Psi^* + \varepsilon^{\mathsf T},$$

with $Z, X$ uncorrelated with $u$ and $\varepsilon$. Instrument $k$ is **relevant** if $\Upsilon^*_{k\cdot} \ne 0$ (set $\mathcal{S}^*$) and **valid** if moreover $\pi^*_k = 0$ (set $\mathcal{V}^*$; $\pi^*_k \ne 0$ encodes a direct pleiotropic effect or instrument–outcome confounding). The reduced form gives $\Gamma^* = \Upsilon^*\beta^* + \pi^*$, so with $\pi_k(\beta) = \Gamma^*_k - \Upsilon^{*\mathsf T}_{k\cdot}\beta$ instrument $k$ **votes** for every $\beta$ on the hyperplane $\mathcal{L}_k = \{\beta : \pi_k(\beta) = 0\}$. Valid instruments all vote for $\beta^*$; invalid ones never do. Assume $\operatorname{rank}(\Upsilon^*_{\mathcal{V}^*\cdot}) = p_d$.

**Generalized plurality rule.** $|\mathcal{V}^*| > \max_{\beta \ne \beta^*}|\mathcal{K}(\beta)|$ with $\mathcal{K}(\beta) = \{k \in \mathcal{S}^* : \pi_k(\beta) = 0\}$. Under it $\beta^*$ is identified as the unique candidate receiving the most votes.

**Proposition (identification failure is rare).** If the entries of $\Upsilon^*_{\mathcal{S}^*\cdot}$ and of $\pi^*$ on the invalid instruments are drawn independently from continuous distributions with full support, while $\pi^*_{\mathcal{V}^*} = 0$ and $\beta^*$ are fixed, then with probability one every false candidate $\beta \ne \beta^*$ receives at most $p_d$ votes; hence if $|\mathcal{V}^*| > p_d$ the generalized plurality rule holds almost surely.

**Theorem (generalized majority rule).** Let $h_0 = 1 + \max\{|\mathcal{H}| : \mathcal{H} \subseteq \mathcal{V}^*,\ \operatorname{rank}\Upsilon^*_{\mathcal{H}\cdot} < p_d\}$, so that any $h_0$ valid instruments have full-rank relevance and $p_d \le h_0 \le |\mathcal{V}^*|$. Then the generalized plurality rule holds whenever

$$|\mathcal{V}^*| > \frac{|\mathcal{S}^*| + h_0 - 1}{2}.$$

For one exposure ($p_d = h_0 = 1$) this is the classical majority rule, more than half of the relevant instruments valid.

## Expansion

A false candidate $\beta \ne \beta^*$ can collect votes from at most $h_0 - 1$ valid instruments, because any $h_0$ valid hyperplanes meet only at $\beta^*$, and from at most all $|\mathcal{S}^*| - |\mathcal{V}^*|$ invalid ones. So $\max_{\beta\ne\beta^*}|\mathcal{K}(\beta)| \le h_0 - 1 + |\mathcal{S}^*| - |\mathcal{V}^*|$, and the majority condition makes this smaller than $|\mathcal{V}^*|$. In the random-coefficient proposition, $p_d + 1$ generic hyperplanes in $\mathbb{R}^{p_d}$ have no common point unless all are valid, which happens on a null set. With one exposure each instrument votes for a single point, while with several exposures it votes for a whole hyperplane, which is why plurality must be counted over intersections.

## Sources

- Ziwei Mei, Qingliang Fan, Zijian Guo, "Identification and Robust Inference for Multiple Treatments with Possibly Invalid Instruments", arXiv (2026). Section 2 (model, full-rank assumption, Generalized Plurality Rule assumption, proposition on random coefficients, Generalized Majority Rule theorem), Mendelian randomization application. <https://doi.org/10.48550/arXiv.2607.21481>
