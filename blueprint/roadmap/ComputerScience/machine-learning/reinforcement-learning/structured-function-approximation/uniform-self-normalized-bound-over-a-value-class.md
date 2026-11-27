# Uniform self-normalized bound over a value-function class

When the regression target $V(x_\tau)$ is itself chosen from data, the self-normalized bound must hold uniformly over a class $\mathcal{V}$ of bounded value functions; a cover of $\mathcal{V}$ in sup norm adds $\log \mathcal{N}_\varepsilon$ and a discretization term $8k^2\varepsilon^2/\lambda$.

**Statement.** Let $(x_\tau)_{\tau \ge 1}$ be a stochastic process on a state space $\mathcal{S}$ with filtration $(\mathcal{F}_\tau)_{\tau \ge 0}$, $x_\tau$ being $\mathcal{F}_\tau$-measurable. Let $(\phi_\tau)_{\tau \ge 1}$ be $\mathbb{R}^d$-valued with $\phi_\tau$ $\mathcal{F}_{\tau-1}$-measurable and $\lVert \phi_\tau \rVert_2 \le 1$, let $\lambda > 0$ and $\Lambda_k = \lambda I + \sum_{\tau=1}^{k} \phi_\tau \phi_\tau^{\mathsf T}$. Let $\mathcal{V}$ be a class of functions $\mathcal{S} \to \mathbb{R}$ with $\sup_x |V(x)| \le H$ for $V \in \mathcal{V}$, and for $\varepsilon > 0$ let $\mathcal{N}_\varepsilon$ be the $\varepsilon$-covering number of $\mathcal{V}$ for $\mathrm{dist}(V,V') = \sup_x |V(x) - V'(x)|$. Then for every $\delta > 0$, with probability at least $1-\delta$, for all $k \ge 0$ and all $V \in \mathcal{V}$,

$$
\Big\lVert \sum_{\tau=1}^{k} \phi_\tau \big\{ V(x_\tau) - \mathbb{E}[V(x_\tau) \mid \mathcal{F}_{\tau-1}] \big\} \Big\rVert^2_{\Lambda_k^{-1}} \le 4H^2 \Big[ \frac{d}{2} \log\Big(\frac{k+\lambda}{\lambda}\Big) + \log \frac{\mathcal{N}_\varepsilon}{\delta} \Big] + \frac{8 k^2 \varepsilon^2}{\lambda}.
$$

The function $V$ may be chosen after seeing the data (for example $V = V^k_{h+1}$ computed from all episodes up to $k$), which is exactly why a fixed-$V$ martingale bound does not suffice.

## Depends on

None.

## Proof depends on

- [Self-normalized bound for vector-valued martingales](self-normalized-bound-for-vector-martingales.md)

## Expansion

Take an $\varepsilon$-cover $\{\tilde V\}$ of $\mathcal{V}$ and write $V = \tilde V + \Delta V$ with $\sup |\Delta V| \le \varepsilon$. By $\lVert u + v \rVert^2 \le 2\lVert u \rVert^2 + 2\lVert v \rVert^2$, the left side is at most twice the same expression for $\tilde V$ plus twice that for $\Delta V$. For each fixed $\tilde V$ the centred terms $\tilde V(x_\tau) - \mathbb{E}[\tilde V(x_\tau) \mid \mathcal{F}_{\tau-1}]$ lie in an interval of length $2H$ and are conditionally $H$-sub-Gaussian, so the self-normalized bound with $V = \lambda I$ and $\det \Lambda_k \le (\lambda + k)^d$ applies, and a union bound over the $\mathcal{N}_\varepsilon$ cover elements gives the first term. The $\Delta V$ term has entries bounded by $2\varepsilon$ and is bounded crudely by $8k^2\varepsilon^2/\lambda$.

The source applies this to the class of LSVI-UCB value functions $V(\cdot) = \min\{\max_a w^{\mathsf T}\phi(\cdot,a) + \beta \sqrt{\phi(\cdot,a)^{\mathsf T}\Lambda^{-1}\phi(\cdot,a)}, H\}$ with $\lVert w \rVert \le L$, $\beta \in [0,B]$, $\lambda_{\min}(\Lambda) \ge \lambda$, whose log-covering number it bounds by $d \log(1 + 4L/\varepsilon) + d^2 \log(1 + 8 d^{1/2} B^2/(\lambda \varepsilon^2))$ (Lemma D.6, via the covering number $(1 + 2R/\varepsilon)^d$ of a Euclidean ball of radius $R$, Lemma D.5).

## Sources

- C. Jin, Z. Yang, Z. Wang and M. I. Jordan, "Provably Efficient Reinforcement Learning with Linear Function Approximation", Conference on Learning Theory (COLT 2020), PMLR 125; journal version Mathematics of Operations Research 48(3):1496–1521, 2023, doi:10.1287/moor.2022.1309. Numbers from arXiv:1907.05388v2: Lemma D.4 (statement and proof), Lemmas D.5 and D.6, Theorem D.3. <https://arxiv.org/abs/1907.05388v2>
