# Correlated pooling improves Dorfman sensitivity under concentration-dependent test errors

**Setting.** Two-stage Dorfman testing of a population of size $N$ in pools of size $n$: each pool is tested, and every member of a positive pool is retested individually. Individual $i$ has viral load $U_i \ge 0$, with prevalence $\alpha = P(U_i > 0)$. A test on a sample with viral load $v$ is positive with probability $p(v)$, where $p(0) = 0$, $p(v) > 0$ for $v > 0$ and $p$ is increasing; results are conditionally independent given viral loads. A pool with loads $\mathbf{v} = (v_1,\dots,v_n)$ has pooled load $h(\mathbf{v})$ for an increasing $h$ (dilution: $h(\mathbf{v}) = \frac1n\sum_i v_i$).

*Naive pooling* (NP) forms pools uniformly at random; *correlated pooling* (CP) places close contacts (household, neighbourhood) in the same pool with probability bounded below. For a uniformly random pool let $S$ be the number of infected members, $Y$ the pooled result, $W_i$ the individual results, $D = \sum_i YW_i$ the positives identified and $\tilde D = \sum_i W_i$. Define

$$
\beta_{\mathrm{P},\alpha} = 1 - \frac{\mathbb{E}_{\mathrm{P},\alpha}[D]}{\mathbb{E}_{\mathrm{P},\alpha}[S]} \quad\text{(overall false negative rate)}, \qquad
\gamma_{\mathrm{P},\alpha} = \frac{\mathbb{E}_{\mathrm{P},\alpha}[D]}{1 + n\,\mathbb{E}_{\mathrm{P},\alpha}[Y]} \quad\text{(positives found per test)},
$$

for $\mathrm{P} \in \{\mathrm{NP},\mathrm{CP}\}$; under a sublinear-association assumption these are the $N \to \infty$ limits of the population-level metrics. Under NP the loads in a pool become independent as $N \to \infty$, while under CP $P_{\mathrm{CP},\alpha}(S > 1 \mid S > 0) > 0$ for every $\alpha$ (infection status is positively correlated between close contacts).

**Statement.**

1. *Sensitivity.* If $p$ is increasing, then $\lim_{\alpha\to 0^+}\beta_{\mathrm{NP},\alpha} \ge \lim_{\alpha\to 0^+}\beta_{\mathrm{CP},\alpha}$, with strict inequality if $p$ and $h$ are strictly increasing.
2. *Effective efficiency.* $\lim_{\alpha\to 0^+}\gamma_{\mathrm{CP},\alpha}/\gamma_{\mathrm{NP},\alpha} \ge (1+\delta)^{-1}$, where $\delta = P_{\mathrm{CP},\alpha}(Y = 1, \tilde D = 0 \mid S > 0)/P_{\mathrm{CP},\alpha}(Y = 1, \tilde D > 0 \mid S > 0)$ is the odds that a positive pool yields no positive on follow-up.
3. *Threshold tests.* If $p(v) = \mathbf{1}\{v \ge u_0\}$ and $h(\mathbf{v}) = \frac1n\sum_i v_i$, then $\lim_{\alpha\to 0^+}\gamma_{\mathrm{CP},\alpha}/\gamma_{\mathrm{NP},\alpha} \ge 1$.

Since the classical efficiency (people screened per test) equals $\gamma_{\mathrm{P},\alpha}/\bigl((1-\beta_{\mathrm{P},\alpha})\alpha\bigr)$, correlated pooling can have *lower* classical efficiency once dilution is modelled, even though it finds more positives per test.

## Expansion

The false negative rate is $\beta_{\mathrm{P},\alpha} = 1 - \mathbb{E}_{\mathrm{P},\alpha}[p(h(\mathbf{V}))\,p(V_1) \mid V_1 > 0]$. Under NP, as $\alpha \to 0$ a positive pool almost surely holds a single positive, so the limit is $1 - \mathbb{E}[p(h(V_1,0,\dots,0))p(V_1) \mid V_1 > 0]$. Under CP, decompose on $S = \ell$: for $\ell \ge 2$ some other $V_i > 0$, so monotonicity gives $h(\mathbf{V}) \ge h(V_1,0,\dots,0)$ and the detection probability is at least the $\ell = 1$ value; since $P(S > 1 \mid S > 0)$ stays positive, the mixture has a smaller false negative rate. Extra positives in a pool raise the pooled concentration and counteract dilution, which is the mechanism behind both results.

## Sources

- Jiayue Wan, Yujia Zhang and Peter I. Frazier, "Correlation Improves Group Testing: Modeling Concentration-Dependent Test Errors", Management Science 72 (2026), 5507–5527, <https://doi.org/10.1287/mnsc.2021.04217>; numbering as in arXiv:2111.07517: Section 3 (single-pool model; main theoretical results on sensitivity, effective efficiency and the threshold-test corollary).
