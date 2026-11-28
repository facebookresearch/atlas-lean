# Semi-discrete exponential scheme for the stochastic SIS model converges strongly with order 1

**Model.** In the stochastic SIS model of Gray et al. (population size $K>0$, contact rate $\beta>0$, recovery rate $\gamma>0$, birth rate $b\ge 0$, noise intensity $\sigma>0$ on the contact rate, $W$ a standard Wiener process), the number of infectives solves

$$
I_t = I_0 + \int_0^t \Big(\eta I_s - \frac{\beta}{K} I_s^2\Big)\,ds + \sigma \int_0^t (K-I_s) I_s\, dW_s, \qquad \eta = \beta - b - \gamma ,
$$

and for $I_0 \in (0,K)$ the solution stays in $(0,K)$ for all $t\ge 0$ almost surely. The explicit Euler–Maruyama scheme does not preserve $(0,K)$.

**Transformation.** With $V(x) = x/(K-x)$, Itô's formula turns $\hat z_t = V(I_t)$ into the SDE

$$
d\hat z_t = \hat F(\hat z_t)\,dt + \sigma K \hat z_t\, dW_t, \qquad \hat F(x) = x\,\phi(x),\quad \phi(x) = \eta - (b+\gamma)x + \frac{\sigma^2K^2 x}{1+x},
$$

whose solution has finite moments $\sup_{t\le T}\mathbb{E}\,\hat z_t^{\,p} < \infty$ of every real order $p$ (Lemma 1).

**Scheme.** Freeze $\phi$ at the left endpoint of each step of size $\Delta \in (0,1)$ and solve the resulting linear SDE exactly (the semi-discrete method):

$$
\hat X_{n+1} = \hat X_n \exp\Big\{\Big(\phi(\hat X_n) - \tfrac12 \sigma^2K^2\Big)\Delta + \sigma K\, \Delta W_n\Big\}, \qquad \hat X_0 = \frac{I_0}{K-I_0},
$$

and transform back by $\hat Y_n = K\hat X_n/(1+\hat X_n)$. The scheme is explicit, $\hat X_n > 0$, and therefore $\hat Y_n \in (0,K)$ for every $n$ (domain preservation).

**Theorem (strong order 1).** For every $q>0$ and $T>0$ there is $C$ independent of $\Delta$ such that

$$
\mathbb{E} \sup_{n = 0,1,\dots,\lceil T/\Delta\rceil} \big|\hat Y_{t_n} - I_{t_n}\big|^q \le C\,\Delta^{q}.
$$

## Proof sketch

The numerical moments satisfy $\mathbb{E}\hat X_n^p \le \hat X_0^p \exp\{(\eta + \sigma^2K^2/2)Tp + p^2\sigma^2K^2T/2\}$, by bounding the exponent's drift and using exponential moments of Brownian motion. The proof of the rate compares $\hat Y_n$ with the logit-Euler scheme $Y_n = Ke^{X_n}/(1+e^{X_n})$, where $X_n$ is the Euler–Maruyama scheme for $z_t = \ln(I_t/(K-I_t))$ with additive noise $\sigma K\,dW$; that scheme is known to have strong order 1. Writing $\hat X_n = e^{\Theta_n}$, both schemes share the noise increment, so $v_n = \Theta_n - X_n$ obeys a noise-free recursion $v_n = v_{n-1} - (b+\gamma)(e^{\Theta_{n-1}} - e^{X_{n-1}})\Delta + \sigma^2K^2 u_{n-1}\Delta$ with $|u_n| = |\hat Y_n - Y_n| \le K|v_n|$. Squaring, Hölder/Young estimates using the moment bounds, and the discrete Gronwall inequality give $\mathbb{E}\sup_n v_n^{2q} \le C\Delta^{2q}$; the triangle inequality transfers the order to $\hat Y_n - I_{t_n}$.

## Sources

- Yiannis Kiouvrekis and Ioannis S. Stamatiou, "Domain preserving and strongly converging explicit scheme for the stochastic SIS epidemic model", *Journal of Computational and Applied Mathematics* 456 (2025), 116219, <https://doi.org/10.1016/j.cam.2024.116219>. Preprint version: arXiv:2307.14404 (2023), Introduction and Section 1 (the semi-discrete scheme, Lemma 1) and Theorem 1, proved in Section 2, <https://doi.org/10.48550/arXiv.2307.14404>.
