# Stochastic compartmental model of fast axonal transport

**Model.** An axon of length $L$ is cut into $N$ sections of length $\delta$ (the motor step size). In section $i$, $Q_i(t)$ particles are on transport (moving at mean speed $v$) and $P_i(t)$ are off transport (paused). With $r = v/\delta$, the transitions are

- lateral transport $(Q_i, Q_{i+1}) \to (Q_i - 1, Q_{i+1} + 1)$ at rate $rQ_i$;
- pausing $(Q_i, P_i) \to (Q_i - 1, P_i + 1)$ at rate $k_1 Q_i$, and resuming $(P_i, Q_i) \to (P_i - 1, Q_i + 1)$ at rate $k_2 P_i$;
- production of new particles into section $1$ at rate $q_0 r$, and removal at the distal end at rate $rQ_N$.

In the extended model, paused particles are deposited into the membrane, $(P_i, D_i) \to (P_i - 1, D_i + 1)$ at rate $k_3 P_i$, and each deposited particle decays at rate $1/\tau$. Let $X_t$ be the distance travelled by a single tagged particle, i.e. $\delta$ times the number of sections it has crossed.

**Theorem.**

1. *(Pure transport.)* If $k_1 = k_2 = 0$, then $X_t/\delta \sim \mathrm{Poisson}(rt)$, so $\mathbb{E}X_t = vt$; as $\delta \to 0$, $X_t/t \to v$ almost surely and $\delta^{-1/2}(X_t - vt) \Rightarrow \sqrt v\, B_t$ for a standard Brownian motion $B$.
2. *(On/off transport.)* If $k_1, k_2 > 0$, the mean velocity $\mathbb{E}X_t/t$ tends to $\frac{k_2}{k_1 + k_2} v$ as $t \to \infty$, and in the limit $\delta \to 0$, as $t \to \infty$,

    $$\frac{X_t}{t} \to \frac{k_2}{k_1+k_2}v \ \text{a.s.}, \qquad \sqrt t\Big(\frac{X_t}{t} - \frac{k_2}{k_1+k_2}v\Big) \Rightarrow \sqrt{\frac{2k_1k_2}{(k_1+k_2)^3}}\; v\, Z, \quad Z \sim N(0,1),$$

    so the wavefront spreads diffusively around the reduced mean speed.

3. *(Equilibrium without deposition.)* The stationary distribution has all $Q_i \sim \mathrm{Poisson}(q_0)$ and $P_i \sim \mathrm{Poisson}(k_1q_0/k_2)$, mutually independent: the axon is homogeneous at equilibrium.
4. *(Equilibrium with deposition.)* With $\rho = \frac{r(k_2 + k_3)}{(r + k_1)(k_2 + k_3) - k_1k_2}$, the stationary distribution has independent

    $$Q_i \sim \mathrm{Poisson}(q_0\rho^i),\quad P_i \sim \mathrm{Poisson}\Big(\frac{k_1}{k_2+k_3}q_0\rho^i\Big),\quad D_i \sim \mathrm{Poisson}\Big(\frac{k_1k_3\tau}{k_2+k_3}q_0\rho^i\Big),$$

    so means and variances decay geometrically along the axon with loss ratio $\rho \approx \exp\big(-\frac{\delta k_1 k_3}{(k_2+k_3)v}\big)$ per section; the mean velocity of non-deposited particles tends to $\frac{k_2+k_3}{k_1+k_2+k_3}v$.

## Expansion

All transitions are first order, so the system is a network of linear (monomolecular) reactions, whose stationary law is a product of Poissons with means solving the deterministic balance equations; with no loss, the balance $rq_{i-1} = rq_i$ forces equal means in every section. A tagged particle alternates exponential runs and pauses, so its position is a renewal-reward process with long-run speed $v$ times the fraction of time on transport, and its fluctuations obey the renewal central limit theorem. Deposition removes particles at a constant per-pause rate, making supply decay geometrically with distance, a quantitative constraint on how far fast transport can supply long axons.

## Sources

- Lea Popovic, Scott A. McKinley and Michael C. Reed, "A Stochastic Compartmental Model for Fast Axonal Transport", SIAM Journal on Applied Mathematics 71 (2011), 1531–1556, <https://doi.org/10.1137/090775385>; numbering as in arXiv:0911.2722: Section 2 (model), Propositions 3.1–3.3, 4.1, 6.1–6.2 and Corollary 6.3.
