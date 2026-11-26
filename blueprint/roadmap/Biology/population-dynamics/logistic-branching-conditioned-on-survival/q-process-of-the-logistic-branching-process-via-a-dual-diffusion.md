# Q-process of the logistic branching process via a dual diffusion

**Logistic branching process.** Each individual gives birth at rate $b = s$, dies naturally at rate $d = \mu$, and dies from competition at rate $c(i-1) = \nu(i-1)$ when the population size is $i$. So the jump rates are $q_{i,i+1} = si$ and $q_{i,i-1} = \mu i + \nu i(i-1)$. The quadratic death rate makes extinction certain even when $s > \mu$, so meaningful long-term behaviour requires conditioning on survival. The **Q-process** $Z^*$ conditions on survival into the indefinite future: $\mathbb Q(Z \in B) = \lim_{u\to\infty}\mathbb P(Z \in B \mid \tau_0 > t + u)$ for $\mathcal F_t$-measurable $B$.

**Dual diffusion.** Let $p$ solve the Wright–Fisher diffusion with selection and one-way mutation

$$dp = \bigl(-\mu p + s\,p(1-p)\bigr)dt + \sqrt{\nu\,p(1-p)}\,dW, \qquad p_0 = 1,$$

with scale density $\mathfrak s(x) = e^{-2sx/\nu}(1-x)^{-2\mu/\nu}$, scale function $S(x) = \int_0^x\mathfrak s$, and speed density $m(x) = e^{2sx/\nu}(1-x)^{2\mu/\nu - 1}(\nu x)^{-1}$. Then the moment duality

$$\mathbb P(Z_t > 0 \mid Z_0 = k) = \mathbb E\bigl[1 - (1 - p_t)^k\bigr]$$

holds. It is obtained from a Moran-type particle construction in which the frequency process converges to $p$ at rate $N^{-1/2}$.

**Theorem.**

1. (Stationary law of the conditioned diffusion.) The diffusion $p$ conditioned never to hit $0$ has stationary density

$$\pi^*(x) = \begin{cases} C\,m(x)S(x)^2, & \mu \ge \nu,\\ C\,m(x)S(x), & \mu < \nu,\end{cases}$$

and it is ergodic when $\mu < \nu$.

2. (Q-process rates.) $Z^*$ is again a birth–death process: $q^*_{i,j} = 0$ for $|i-j| > 1$, and

$$q^*_{k,k+1} = q_{k,k+1}\,r^*_{k+1,k}\ (k \ge 1), \qquad q^*_{k,k-1} = q_{k,k-1}\,r^*_{k-1,k}\ (k \ge 2), \qquad r^*_{i,j} = \frac{\int_0^1\bigl(1-(1-\zeta)^i\bigr)\pi^*(\zeta)\,d\zeta}{\int_0^1\bigl(1-(1-\zeta)^j\bigr)\pi^*(\zeta)\,d\zeta}.$$

Moreover there is $C > 0$, independent of $k$, with $1/C < r^*_{k-1,k} \le r^*_{k+1,k} < C$.

3. (Finite horizon.) Conditioning on survival up to time $T$ gives a time-inhomogeneous birth–death process with rates $q^T_{k,k\pm1}(t) = q_{k,k\pm1}\,r^T_{k\pm1,k}(T-t)$, where $r^T_{i,j}(t) = \mathbb E[1-(1-p_t)^i]/\mathbb E[1-(1-p_t)^j]$.

Because the Q-process has a non-trivial stationary distribution, the Yaglom limit of $Z_t \mid Z_t > 0$ needs no normalization. The conditioned population size stays of order one, with birth rates boosted and death rates damped by uniformly bounded factors.

## Expansion

Doob's $h$-transform with $h(k) = \lim_u\mathbb P_k(\tau_0 > u)/\mathbb P_1(\tau_0 > u)$ gives $q^*_{k,j} = q_{k,j}h(j)/h(k)$. By duality, $\mathbb P_k(\tau_0 > u) = \mathbb E[1 - (1-p_u)^k]$. On the event of survival, $p_u$ is distributed for large $u$ approximately as $\pi^*$, so the ratio of survival probabilities converges to $r^*_{j,k}$. The diffusion $p$ is absorbed at $0$ (the dual of survival), and conditioning it to avoid $0$ is itself an $h$-transform by the scale function. That is why $\pi^*$ is the speed measure multiplied by $S$ or $S^2$, depending on whether the boundary $1$ is accessible. Bounds on $1 - (1-\zeta)^{k\pm1}$ relative to $1 - (1-\zeta)^k$ give the uniform constants.

## Sources

- Alison Etheridge, Shidong Wang, Feng Yu, "Conditioning the logistic branching process on non-extinction", arXiv (2013). Section 1 (Definitions 1.1–1.4, Theorem 1.5), Section 2 (dual SDE, Propositions 2.1, 2.3, 2.4), Section 3 (Proposition 3.1). <https://doi.org/10.48550/arXiv.1310.5766>
