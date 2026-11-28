# Exponential convergence to the QSD and metastable extinction time of multitype birth-and-death processes

**Model.** Let $\mathbf{B}, \mathbf{D} : \mathbb{R}_+^d \to \mathbb{R}_+^d$ be vector fields and $K > 0$ a scale parameter. The $d$-type birth-and-death process $\mathbf{N}^K(t) \in \mathbb{Z}_+^d$ jumps from $\mathbf{n}$ to $\mathbf{n} + \mathbf{e}_j$ at rate $K B_j(\mathbf{n}/K)$ and to $\mathbf{n} - \mathbf{e}_j$ at rate $K D_j(\mathbf{n}/K)$. Its fluid limit (Kurtz's theorem, on bounded time intervals as $K \to \infty$) is $\dot{\mathbf{x}} = \mathbf{B}(\mathbf{x}) - \mathbf{D}(\mathbf{x})$.

**Hypotheses.** (H0) $\mathbf{B}, \mathbf{D}$ are locally Lipschitz with nonnegative components; (H1) $\mathbf{B}(\mathbf{x}) = 0 \iff \mathbf{D}(\mathbf{x}) = 0 \iff \mathbf{x} = 0$, and $0$ is linearly unstable for $\mathbf{B} - \mathbf{D}$; (H2) there is an interior fixed point $\mathbf{x}^* \in \operatorname{int}\mathbb{R}_+^d$; (H3) for some $\beta > 0$ and $R > \|\mathbf{x}^*\|$, $\langle \mathbf{B}(\mathbf{x}) - \mathbf{D}(\mathbf{x}), \mathbf{x} - \mathbf{x}^* \rangle \le -\beta \|\mathbf{x}\| \|\mathbf{x} - \mathbf{x}^*\|^2$ for $\|\mathbf{x}\| < R$; (H4) a geometric condition placing a ball around $\mathbf{x}^*$ inside $\{|\mathbf{y}| \le L\} \subset \mathcal{B}(0,R)$; (H5) $\sup_{s > L} B_{\max}(s)/D_{\min}(s) < 1/2$, where $B_{\max}(s) = \sup_{|\mathbf{x}| = s} \sum_j B_j(\mathbf{x})$ and $D_{\min}(s) = \inf_{|\mathbf{x}| = s} \sum_j D_j(\mathbf{x})$; (H6) $D_{\min}$ is eventually monotone with $\int_1^\infty ds/D_{\min}(s) < \infty$; (H7) $\inf_{\mathbf{x}} \min_j D_j(\mathbf{x})/\max_\ell x_\ell > 0$; (H8) $\min_j \partial_{x_j} B_j(0) > 0$. Under these hypotheses $\mathbf{N}^K$ is absorbed at $0$ almost surely. Write $T_0$ for the absorption time and $\mathcal{D} = \mathbb{Z}_+^d \setminus \{0\}$.

**Theorem.**

1. *(QSD and uniform exponential convergence.)* There are $K_0 > 1$, $c \in (0,1)$ and $0 < a < b$ such that for every $K \ge K_0$ there is $t_0(K) \in (a \log K, b \log K)$ and a unique probability measure $\nu_K$ on $\mathcal{D}$ with, for every initial law $\mu$ on $\mathcal{D}$ and all $t \ge 0$,

$$
\big\| \mathbb{P}_\mu\big(\mathbf{N}^K(t) \in \cdot \mid t < T_0\big) - \nu_K \big\|_{TV} \le 2 (1-c)^{\lfloor t / t_0(K) \rfloor}.
$$

   In particular $\nu_K$ is the unique quasi-stationary distribution, and $\mathbb{P}_{\nu_K}(T_0 > t) = e^{-\lambda_0(K) t}$ for some $\lambda_0(K) > 0$.
2. *(Exponentially long persistence.)* There are $K_0$ and $d_1 > d_2 > 0$ with $e^{-d_1 K} \le \lambda_0(K) \le e^{-d_2 K}$ for $K > K_0$; starting from the QSD the mean extinction time $1/\lambda_0(K)$ is exponentially large in $K$.
3. *(Mixture approximation of the law.)* With $\omega(K) = -\log(1-c)/t_0(K) \ge C'/\log K$, there are constants $C, \eta > 0$ and, for each $\mathbf{n} \in \mathcal{D}$, a number $p_K(\mathbf{n}) \in (c, 1]$ such that for all $t \ge 0$ and $K > K_0$

$$
\sup_{\mathbf{n} \in \mathcal{D}} \Big\| \mathbb{P}_{\mathbf{n}}(\mathbf{N}^K(t) \in \cdot) - e^{-\lambda_0(K) t} p_K(\mathbf{n})\, \nu_K - \big(1 - e^{-\lambda_0(K) t} p_K(\mathbf{n})\big) \delta_0 \Big\|_{TV} \le 2 e^{-\eta K} e^{-\lambda_0(K) t} + C e^{-\omega(K) t}.
$$

So after a relaxation time of order $\log K$ the population is distributed as a mixture of the QSD and the extinct state, and it leaves the QSD only on the time scale $e^{\Theta(K)}$.

## Expansion

The proof checks the two Champagnat–Villemonais conditions for uniform exponential convergence: (A1) a uniform Doeblin-type minorization of the conditioned law on a small set, and (A2) a comparison of survival probabilities from different starting points. Hypothesis (H3) makes $\varphi$, built from $\|\mathbf{x} - \mathbf{x}^*\|^2$, a Lyapunov function whose generator satisfies $\mathcal{L}_K \varphi \le -\tfrac{\alpha\beta}{2} \tfrac{\|\mathbf{n}\|}{K} \tfrac{\|\mathbf{n} - \mathbf{n}^*\|^2}{K} \varphi$ outside a $\sqrt{K}$-neighbourhood of $\mathbf{n}^* = K\mathbf{x}^*$; (H5)–(H6) bring very large populations down to $\{|\mathbf{n}| \le LK\}$ in bounded time; (H8) pushes small populations away from $0$; and a "four domains" argument shows that from any state the process enters a neighbourhood of $\mathbf{n}^*$ within time $O(\log K)$ with probability bounded below, which produces the $\log K$ mixing scale. The source proves both bounds on $\lambda_0(K)$ directly (the upper bound alone would also follow from large-deviation asymptotics for jump processes), and item 3 from a spectral analysis of the semigroup on $\ell^\infty$, whose resolvent has a unique simple pole at $-\lambda_0(K)$ in $\Re z > -\omega(K)$.

## Sources

- J.-R. Chazottes, P. Collet, S. Méléard, "On time scales and quasi-stationary distributions for multitype birth-and-death processes", arXiv:1702.05369 (2017): Section 2 (hypotheses (H0)–(H8), generator, Proposition 2.1), Theorems 3.1, 3.2, 3.3 and 3.4, Theorem 4.1 and Corollary 4.2 (Lyapunov function), Section 4.2 (four domains), Section 5 (conditions (A1)–(A2)). <https://doi.org/10.48550/arXiv.1702.05369> Published version: Annales de l'Institut Henri Poincaré, Probabilités et Statistiques 55 (2019) 2249–2294, <https://doi.org/10.1214/18-aihp948>.
