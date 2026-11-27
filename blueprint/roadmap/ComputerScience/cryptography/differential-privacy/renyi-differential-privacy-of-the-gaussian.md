# Rényi differential privacy of the Gaussian mechanism

For probability distributions $P$ and $Q$ on $\mathbb{R}$ with densities and $\alpha > 1$, the *Rényi divergence of order $\alpha$* is
$D_\alpha(P \,\|\, Q) = \frac{1}{\alpha - 1} \log \mathbb{E}_{x \sim Q}\left[(P(x)/Q(x))^\alpha\right]$, with natural logarithms. A randomized mechanism $f$ satisfies
*$(\alpha, \varepsilon)$-Rényi differential privacy* if $D_\alpha(f(D) \,\|\, f(D')) \le \varepsilon$ for all adjacent inputs $D$, $D'$.

**Proposition.** For $\sigma > 0$ and $\mu \in \mathbb{R}$, $D_\alpha(\mathcal{N}(0, \sigma^2) \,\|\, \mathcal{N}(\mu, \sigma^2)) = \alpha \mu^2 / (2\sigma^2)$ for every $\alpha > 1$.

**Corollary.** If a real-valued query $f$ has sensitivity $1$, that is $|f(D) - f(D')| \le 1$ for adjacent $D$, $D'$, then the Gaussian mechanism
$D \mapsto f(D) + Z$ with $Z \sim \mathcal{N}(0, \sigma^2)$ satisfies $(\alpha, \alpha / (2\sigma^2))$-Rényi differential privacy for every $\alpha > 1$.

## Depends on

- [Differential privacy](differentially-private.md)

## Sources

- I. Mironov, "Rényi differential privacy", *IEEE CSF 2017*, <https://arxiv.org/abs/1702.07476>: Definition 3 (Rényi divergence), Definition 4 ($(\alpha, \varepsilon)$-RDP), Proposition 7 with its proof, and Corollary 3.
