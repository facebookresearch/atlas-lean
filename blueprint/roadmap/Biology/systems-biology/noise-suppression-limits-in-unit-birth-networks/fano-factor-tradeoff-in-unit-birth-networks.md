# Fano-factor tradeoff in unit-birth networks

**Model.** A continuous-time Markov chain $X$ on $\mathbb Z_{\ge0}^N$, $N\ge2$, with generator

$$(L\varphi)(x)=\sum_{i=1}^Nf_i(x_{-i})\big(\varphi(x+e_i)-\varphi(x)\big)+\sum_{i=1}^N\frac{x_i}{\tau_i}\big(\varphi(x-e_i)-\varphi(x)\big):$$

component $i$ is produced one molecule at a time at a rate $f_i\ge0$ that may depend on all other components but not on $x_i$ itself, and degraded linearly with lifetime $\tau_i>0$. Noise is measured by the Fano factor $F_{X_i}=\operatorname{Var}_\pi X_i/\mathbb E_\pi X_i$ under the stationary law $\pi$ (Poisson baseline $1$). Write $\mu_i=\mathbb E_\pi f_i(X_{-i})$.

**Theorem.** Under standing hypotheses (irreducibility and a stationary law, finite second moments, positive mean birth rates, and at most linear growth of the total jump rate):
1. $\mathbb E_\pi X_i=\tau_i\mu_i$ and $F_{X_i}=1+\operatorname{Cov}_\pi\big(f_i(X_{-i}),X_i\big)/\mu_i$;
2. the single-component information flow $\dot I_{X_i}$ (the stationary rate at which births and deaths of $X_i$ change the mutual information between $X_i$ and the rest) is well defined and $\frac{F_{X_i}-1}{\tau_i}\ge\dot I_{X_i}$;
3. $\sum_i\dot I_{X_i}=0$.

Consequently, for **any** network topology and rate functions,

$$\sum_{i=1}^N\frac{F_{X_i}-1}{\tau_i}\ \ge\ 0,$$

so uniform sub-Poissonian suppression is impossible: if $F_{X_k}<1$ for some $k$, then $F_{X_j}>1$ for some $j\ne k$. The hypotheses hold whenever $f_i\ge\varepsilon>0$ for all $i$ and $\sum_if_i(x_{-i})\le A+B\|x\|_1$ with $B<1/\tau_{\max}$.

**Theorem (signed monotonicity).** If there is a sign vector $\sigma\in\{\pm1\}^N$ such that each $f_i$ is monotone for the order $\preceq_\sigma$ (equivalently, when each dependence is monotone, every cycle of the undirected signed interaction graph has positive parity, i.e. the network is structurally balanced), then $\operatorname{Cov}_\pi(f_i(X_{-i}),X_i)\ge0$ and $F_{X_i}\ge1$ for every $i$: no component at all can be sub-Poissonian.

## Depends on

- [Intrinsic and extrinsic gene expression noise](../intrinsic-and-extrinsic-gene-expression-noise/README.md)

## Expansion

The Fano identity comes from applying the stationarity relation $\mathbb E_\pi L\varphi=0$ to $\varphi=x_i$ and $\varphi=x_i^2$. Marginal flux balance $\pi_i(n)m_i(n)=\frac{n+1}{\tau_i}\pi_i(n+1)$, with $m_i(n)$ the conditional mean birth rate, lets one write $\dot I_{X_i}$ as a sum of fluxes times log-ratios of conditional probabilities; a log-sum (Jensen) inequality compares it with the covariance term, giving item 2. Item 3 holds because the total entropy production of the logarithmic potential $-\log\pi$ vanishes in stationarity, $\mathbb E_\pi L(-\log\pi)=0$; the technical core is justifying this on an infinite state space, via weighted entropy-tail bounds $\sum\pi(1+\|x\|)|\log\pi|<\infty$ from second moments. For signed-monotone networks the dynamics are monotone for $\preceq_\sigma$, so the stationary law is associated (positively correlated for increasing functions), which makes each covariance non-negative. This proves, for unit-birth models, the 2019 conjecture of Paulsson and collaborators on fundamental limits of noise suppression, along the information-theoretic route proposed by Ripsman, Kell and Hilfinger.

## Sources

- D. F. Anderson, "Noise tradeoffs, stationary information flow, and structural balance in unit-birth networks", arXiv:2605.15401 (2026), Section 2 (generator, Assumption 2.1, Definition 1, Theorems 1-2), Section 3 (Lemmas 1-6) and Section 5 (Assumption 5.1, Proposition 1, Theorem 3, Propositions 2-4), <https://doi.org/10.48550/arXiv.2605.15401>.
