# Quasi-stationary distributions of the discrete-time binomial SIS model

**Deterministic model.** Per time step, individuals escape death with probability $e^{-\mu}$, infected individuals escape recovery with probability $e^{-\gamma}$, and surviving susceptibles escape infection with probability $e^{-\beta I_n}$ ($\mu,\gamma,\beta>0$, constant population). The infected fraction obeys

$$I_{n+1} = F(I_n) = e^{-\mu}(1-I_n)\big(1 - e^{-\beta I_n}\big) + e^{-\mu-\gamma}I_n, \qquad I_n \in [0,1].$$

The growth rate at the disease-free state is $\alpha = \beta e^{-\mu} + e^{-\mu-\gamma}$ and the basic reproduction number is $R_0 = \beta e^{-\mu}/(1 - e^{-\mu-\gamma})$; $\alpha > 1 \iff R_0 > 1$. If $R_0 \le 1$, $0$ is globally asymptotically stable; if $R_0 > 1$, there is a unique positive fixed point $I^* \in (0,1]$, globally stable on $(0,1]$.

**Stochastic model.** With population size $N$,

$$I_{n+1} = \frac{X_{n+1} + Y_{n+1}}{N}, \qquad X_{n+1} \sim \mathrm{Binom}\big(NI_n,\,e^{-\mu-\gamma}\big), \qquad Y_{n+1} \sim \mathrm{Binom}\big(N(1-I_n),\,e^{-\mu}(1 - e^{-\beta I_n})\big),$$

whose mean-field dynamics is $F$. Extinction ($I_n = 0$) occurs in finite time almost surely, for all $R_0$. The substochastic transition matrix on $\{1/N,\dots,1\}$ has a dominant eigenvalue $\lambda^N \in (0,1)$ with left eigenvector $\pi^N$, the quasi-stationary distribution (QSD); $1/(1-\lambda^N)$ is the intrinsic mean time to extinction.

**Theorem.** (i) If $\alpha \le 1$ ($R_0 \le 1$), then $\lambda^N \le \alpha$ for all $N$, so the intrinsic mean time to extinction is at most $1/(1-\alpha)$, and $\pi^N \to \delta_0$ weakly. (ii) If $\alpha > 1$ ($R_0 > 1$), then $\pi^N \to \delta_{I^*}$ weakly and

$$\limsup_{N\to\infty}\frac1N\log\big(1 - \lambda^N\big) < 0,$$

i.e. the intrinsic mean time to extinction grows exponentially in $N$: $1/(1-\lambda^N) \ge c_1e^{c_2N}$.

**SIR analogue.** For the corresponding discrete-time SIR model with births balancing deaths, the same $\alpha$ governs the deterministic dynamics (global stability of $(1,0)$ if $\alpha \le 1$, a compact global attractor in the interior if $\alpha > 1$), and for the binomial stochastic model: if $\alpha < 1$ then $\lambda^N \le \alpha$ and $\pi^N \to \delta_{(1,0)}$; if $\alpha > 1$ then $1-\lambda^N$ decays exponentially in $N$, every weak limit point of $\pi^N$ is supported on a compact subset of $(0,1)^2$ and invariant for the deterministic map, and $\pi^N \to \delta_{(S^*,I^*)}$ whenever the deterministic model has a globally stable hyperbolic endemic fixed point (e.g. for small recovery rates).

## Expansion

For $\alpha \le 1$, comparing the expected number of infected individuals with a subcritical branching process gives $\mathbb E[NI_{n+1}\mid I_n] \le \alpha NI_n$, which bounds the persistence probability per step under the QSD by $\alpha$. For $\alpha > 1$, large deviation estimates for binomial sums show that leaving a neighbourhood of the deterministic attractor costs probability $e^{-N\rho(\delta)}$, while the deterministic flow pushes away from $0$; combined with the weak* limit of QSDs being invariant for the mean-field map, this yields concentration on the attractor and exponentially long extinction times.

## Sources

- Sebastian J. Schreiber, Shuo Huang, Jifa Jiang and Hao Wang, "Extinction and quasi-stationarity for discrete-time, endemic SIS and SIR models", arXiv:2005.08312 (2020), Section 2 (global dynamics of the deterministic SIS map), Section 3 (stochastic SIS model, almost sure extinction and main quasi-stationarity theorem), Sections 4–5 (deterministic and stochastic SIR models) and the large-deviation propositions in the proofs, <https://doi.org/10.48550/arXiv.2005.08312>.
