# Universal large-time clone size distribution

**Model.** A wild-type population grows deterministically with size $n_\tau$, $\tau \ge 0$. Mutant clones are initiated as an inhomogeneous Poisson process with intensity $\mu n_\tau$, and each clone grows as a birth–death branching process with birth rate $1$ and death rate $\beta \in [0,1)$, so mutant fitness is $\lambda = 1 - \beta > 0$. Let $a_t = \int_0^t n_\tau\,d\tau$. A clone sampled uniformly among those initiated by time $t$ has size $Y_t$ with

$$P(Y_t = k) = \frac{1}{a_t}\int_0^t n_\tau\, P(Z_{t-\tau} = k)\,d\tau, \qquad Z_t(s) = \mathbb{E}\,s^{Z_t} = 1 - \frac{\lambda}{1 - \xi e^{-\lambda t}},\ \ \xi = \frac{\beta - s}{1 - s},$$

where $Z_t$ is the birth–death process started from one cell. In particular $P(Z_t = k) = (1 - \beta/S_t)(S_t - 1)S_t^{-k}$ for $k \ge 1$, with $S_t = (1 - \beta e^{-\lambda t})/(1 - e^{-\lambda t})$.

**Assumption.** $n_\tau = 0$ for $\tau < 0$, $n_\tau$ is positive, continuous and nondecreasing for $\tau > 0$, and $\lim_{t\to\infty} n_{t-x}/n_t$ exists in $(0,\infty)$ for each $x \ge 0$. Then $n_{t-x}/n_t \to e^{-x\delta^*}$ where $\delta^* = \lim_{t\to\infty} (\log n_t)/t \ge 0$; set $\gamma^* = \delta^*/\lambda$.

**Theorem.**
1. (Finite time.) For each finite $t$, $P(Y_t = k) = S_t^{-k}\,\Theta_t(k)$ with $\Theta_t$ subexponential in $k$, so the distribution has an exponential cut-off at $k$ of order $e^{\lambda t}$, which disappears as $t \to \infty$.
2. (Large time, exponential-type growth $\delta^* > 0$.) For $k \ge 1$,

$$\lim_{t\to\infty} P(Y_t = k) = \frac{\delta^*\,\Gamma(k)}{(\gamma^* + 1)_k}\; {}_2F_1\!\left(k, \gamma^*; \gamma^* + 1 + k; \beta\right),$$

with $(x)_k$ the rising factorial.
3. (Immortal mutants, $\beta = 0$, $\delta^* > 0$.) $Y_t$ converges to the Yule–Simon distribution, $\lim_{t\to\infty} P(Y_t = k) = \delta^*\,\Gamma(k)\,/\,(\delta^*+1)_k$; for neutral mutants ($\delta^* = 1$) this is $1/(k(k+1))$.
4. (Power-law tail.) For any growth satisfying the assumption,

$$\lim_{k\to\infty}\lim_{t\to\infty} k^{\gamma^* + 1}\,\frac{a_t}{n_t}\,P(Y_t = k) = \frac{\Gamma(1 + \gamma^*)}{\lambda^{\gamma^*}},$$

so the large-time tail decays as $k^{-(1+\gamma^*)}$, and as $k^{-1}$ for subexponential wild-type growth ($\gamma^* = 0$).

## Expansion

Conditioning on the initiation time turns the clone size into a mixture of geometric-type laws, so its generating function is $a_t^{-1}\int_0^t n_\tau Z_{t-\tau}(s)\,d\tau$. Its singularity closest to the origin is at $s = S_t > 1$, which gives the finite-time cut-off. As $t \to \infty$, the initiation-time density seen backwards from $t$ converges to an exponential with rate $\delta^*$ (or flattens when $\delta^* = 0$), and integrating the birth–death generating function against it gives a hypergeometric limit, $(a_t/n_t)(Y_t(s) - \beta) \to \frac{1}{\gamma^*}\big(1 - {}_2F_1(1,\gamma^*;1+\gamma^*;\xi)\big)$. Singularity analysis at $s = 1$ then gives the power-law tail. The exponent depends on the wild-type growth only through the single number $\delta^*$, which is why the same two-parameter form covers exponential, power-law and logistic growth; the classical Luria–Delbrück setting is the exponential case. Analysis of metastasis size data favored a power-law over an exponential tail.

## Sources

- M. D. Nicholson, T. Antal, "Universal asymptotic clone size distribution for general population growth", Bulletin of Mathematical Biology 78 (2016), Equations (1)–(9), Theorem 1, Assumption 1, Lemma 1, Theorem 3 and Corollaries 1–3, <https://doi.org/10.1007/s11538-016-0221-x>, PMCID PMC5090018.
