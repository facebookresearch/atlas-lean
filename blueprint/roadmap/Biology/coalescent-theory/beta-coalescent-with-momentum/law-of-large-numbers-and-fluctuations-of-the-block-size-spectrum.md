# Law of large numbers and fluctuations of the block size spectrum of the Beta-coalescent with momentum

**Setting.** Take the dynamic random graph with $\Theta = \Lambda\times\delta_1$ (every selected group is joined into a complete graph, $\theta = 0$) and the Beta measure
$$\Lambda(du) = u^{\alpha-1}(1-u)^{\beta-1}\,du,\qquad \alpha \in (0,1),\ \beta > 0.$$
Let $\mathtt{C}^n_t$ be the block size spectrum up to order $d$ of the associated coalescent with momentum on $n$ vertices, started from singletons, and define the rescaled, normalized spectrum
$$\mathbf{C}^n_t = \frac{1}{n}\,\mathtt{C}^n_{n^{\alpha-1}t}.$$
For $\mathbf{l} \in \mathbb{N}^d$ write $|\mathbf{l}| = \sum_j \ell_j$, $\|\mathbf{l}\| = \sum_j j\ell_j$, and let $\mathcal{P}_{2+}(i) = \{\mathbf{l} : \|\mathbf{l}\| = i,\ \ell_i = 0\}$ be the integer partitions of $i$ into at least two parts.

**Theorem (dynamic law of large numbers).** For all $\varepsilon, T > 0$, $\mathbb{P}\big(\sup_{t\le T}|\mathbf{C}^n_t - \mathbf{c}_t| > \varepsilon\big) \to 0$, where $\mathbf{c}_t$ solves
$$\frac{d}{dt}c_{t,i} = \sum_{\mathbf{l}\in\mathcal{P}_{2+}(i)}\prod_{j=1}^d\frac{(j\,c_{t,j})^{\ell_j}}{\ell_j!}\,\Gamma(\alpha + |\mathbf{l}| - 2) - \frac{\Gamma(\alpha)}{1-\alpha}\,i\,c_{t,i} =: F_i(\mathbf{c}_t),\qquad c_{0,i} = \delta_{i,1}.$$
Moreover $\sup_{t\le T}\mathbb{E}\|\mathbf{C}^n_t - \mathbf{c}_t\|_2^2 = O(n^{\alpha-1})$.

**Explicit solution.** With $\gamma = \Gamma(\alpha)/(1-\alpha)$, $c_{t,i} = p_i(t)e^{-i\gamma t}$ where $p_i$ is a polynomial of degree $i-1$ given recursively by
$$p_i(t) = c_{0,i} + \sum_{\mathbf{l}\in\mathcal{P}_{2+}(i)}\Gamma(\alpha + |\mathbf{l}| - 2)\prod_{j=1}^d\frac{j^{\ell_j}}{\ell_j!}\int_0^t\prod_{j=1}^d p_j(s)^{\ell_j}\,ds;$$
for example $p_2(t) = c_{0,2} + \frac{\Gamma(\alpha)}{2}c_{0,1}^2\,t$.

**Theorem (functional limit theorem).** Let $\sigma_n = n^{(1-\alpha)/(2-\alpha)}$ and $\mathbf{U}^n_t = \sigma_n(\mathbf{C}^n_t - \mathbf{c}_t)$. There is a Poisson point process $\mathcal{N}$ on $[0,\infty)\times(0,\infty)$ with intensity $dt\,u^{\alpha-3}\,du$, on the same probability space, such that $\sup_{t\le T}|U^n_{t,i} - U_{t,i}| \to 0$ in probability, where $\mathbf{U}$ is the generalized Ornstein–Uhlenbeck process
$$dU_{t,i} = \langle\nabla F_i(\mathbf{c}_t), \mathbf{U}_t\rangle\,dt - i\,c_{t,i}\,dL_t,$$
with $L$ the spectrally positive Lévy process with Lévy measure $u^{\alpha-3}\,du$ driven by $\mathcal{N}$ (compensated).

## Depends on

- [Dynamic Θ-random graph and the Λ-coalescent with momentum](dynamic-random-graph-and-the-lambda-coalescent-with-momentum.md)

## Expansion

Each vertex is hit by a non-silent $u$-merger at total rate $\int u(1-(1-u)^{n-1})\,u^{\alpha-3}(1-u)^{\beta-1}du = n^{1-\alpha}\Gamma(\alpha)/(1-\alpha) + O(1)$, which fixes the time scale $n^{\alpha-1}$ and the loss term $\gamma\,i\,c_{t,i}$. Rescaling the merger fraction as $u = y/n$ turns the Beta density into $y^{\alpha-3}dy$, and a block of size $j$ joins a merger with probability about $jy/n$; summing over which small blocks combine into a block of size $i$ gives the gain term with $\int y^{|\mathbf{l}|}e^{-y}y^{\alpha-3}dy = \Gamma(\alpha + |\mathbf{l}| - 2)$. A Poisson integral representation coupling all $n$ through the consistent graph process makes the drift converge uniformly. Fluctuations come from rare large mergers, with $u$ of order $\sigma_n^{-1}$, which remove a fraction of every size class at once; this yields heavy-tailed, non-Gaussian noise of index $2 - \alpha$ and the unusual normalization $\sigma_n$.

## Sources

- Frederic Alberti, Florin Boenkost and Fernando Cordero, "On the block size spectrum of a class of exchangeable dynamic random graphs", arXiv:2406.08972 (2024), Definition 2.4, Theorem 2.5, Corollary 2.6 and Theorems 2.7 and 2.8, <https://doi.org/10.48550/arXiv.2406.08972>.
