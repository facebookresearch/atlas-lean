# Generalized linear chain trick for phase-type dwell times

**Phase-type distributions.** A continuous phase-type distribution with parameters $(\boldsymbol\alpha, \mathbf A)$ is the law of the absorption time of a continuous-time Markov chain with $k$ transient states and one absorbing state, started from the distribution $\boldsymbol\alpha \in [0,1]^k$ on the transient states (with $\alpha_* = 1 - \mathbf 1^{\mathsf T}\boldsymbol\alpha$ the probability of starting absorbed). Here $\mathbf A$ is the $k\times k$ transient block of the rate matrix: off-diagonal entries are non-negative, diagonal entries are minus the total exit rates, and $\mathbf a = -\mathbf A\mathbf 1$ is the vector of absorption rates. The density, distribution function and moments are

$$f(t) = \boldsymbol\alpha^{\mathsf T} e^{\mathbf A t}(-\mathbf A\mathbf 1), \qquad F(t) = 1 - \boldsymbol\alpha^{\mathsf T} e^{\mathbf A t}\mathbf 1, \qquad \mathbb E(Y^j) = j!\, \boldsymbol\alpha^{\mathsf T}(-\mathbf A)^{-j}\mathbf 1.$$

Erlang, hypoexponential (generalized Erlang) and Coxian laws are special cases; the class is closed under convolution, minima, maxima and finite mixtures.

**Theorem (GLCT).** Suppose individuals enter a state X at rate $\mathcal I(t)$ and the time spent in X is phase-type with parameters $(\boldsymbol\alpha, \mathbf A)$. Partition X into sub-states $X_1, \dots, X_k$ with amounts $\mathbf x(t) = (x_1, \dots, x_k)^{\mathsf T}$. Then the mean-field equations are

$$\frac{d\mathbf x}{dt} = \boldsymbol\alpha\, \mathcal I(t) + \mathbf A^{\mathsf T}\mathbf x(t),$$

the outflow from the sub-states is $(-\mathbf A\mathbf 1) \circ \mathbf x$ (Hadamard product), and the total outflow from X is $(-\mathbf A\mathbf 1)^{\mathsf T}\mathbf x$.

**Corollary (linear chain trick).** If the dwell time is hypoexponential with rates $r_1, \dots, r_k > 0$ (Erlang with rate $r = k/\tau$ and mean $\tau$ when all $r_i = r$), then

$$\dot x_1 = \mathcal I(t) - r_1 x_1, \qquad \dot x_i = r_{i-1}x_{i-1} - r_i x_i, \quad i = 2, \dots, k.$$

**Competing exponential exits.** If the dwell time in X is $T = \min_i T_i$ with independent $T_i \sim \mathrm{Exp}(r_i)$, and an individual exiting because $T = T_i$ moves to state $Y_\ell$ with probability $p_{i\ell}$, the mean-field model is the same as one with dwell time $\mathrm{Exp}(r)$, $r = \sum_i r_i$, and exit probabilities $p_\ell = \sum_i p_{i\ell} r_i / r$.

**Expected rewards.** If time in transient state $i$ accrues reward at rate $g_i$, the expected total reward before absorption is $\boldsymbol\alpha^{\mathsf T}(-\mathbf A^{-1})\mathbf g$; with $\mathbf g = \mathbf 1$ this is the mean dwell time. The minimum of an $\mathrm{Exp}(\mu)$ time and an independent hypoexponential time with rates $\lambda_1, \dots, \lambda_k$ is Coxian with $\boldsymbol\alpha = \mathbf e_1$ and bidiagonal generator with diagonal $-(\lambda_i + \mu)$ and superdiagonal $\lambda_i$, with mean

$$\sum_{j=1}^k \frac{1}{\lambda_j + \mu} \prod_{i=1}^{j-1}\frac{\lambda_i}{\lambda_i + \mu}.$$

## Proof sketch

The mean-field amount in sub-state $j$ at time $t$ is the integral over past entry times $s$ of $\mathcal I(s)$ times the probability that an individual entering at $s$ is in phase $j$ at time $t$, namely $(\boldsymbol\alpha^{\mathsf T} e^{\mathbf A(t-s)})_j$. Differentiating this convolution gives the linear ODE with input $\boldsymbol\alpha\,\mathcal I(t)$ and matrix $\mathbf A^{\mathsf T}$; the Erlang chain is the special case of a bidiagonal $\mathbf A$ with $\boldsymbol\alpha = \mathbf e_1$. The reward formula holds because $-\mathbf A^{-1}$ is the Green matrix whose $(i,j)$ entry is the expected time spent in $j$ starting from $i$. Writing compartmental models in this matrix-vector form lets threshold quantities be computed for arbitrary numbers of sub-states at once.

## Sources

- Paul J. Hurtado and Cameron Richards, "Finding Reproduction Numbers for Epidemic Models and Predator-Prey Models of Arbitrary Finite Dimension Using the Generalized Linear Chain Trick", *Bulletin of Mathematical Biology* 87 (2025), 89, <https://doi.org/10.1007/s11538-025-01467-5>. Preprint version: arXiv:2008.06768 (2020), Section 2.1, Theorem 1, Corollary 1 and Theorem 2 (Section 2.2), Theorems 5 and 6 (appendices), <https://doi.org/10.48550/arXiv.2008.06768>.
