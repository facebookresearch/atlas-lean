# Stationary immunity distribution under random drift and transmissibility

**Model.** Between seasons the virus undergoes a random genetic drift $\delta_k \in [0,1]$, multiplying residual protection so that previously infected individuals regain susceptibility, and receives a new random transmissibility $\tau_k$; the pairs $(\delta_k, \tau_k)$ are i.i.d. with joint density $q$. In the one-season-memory version, $p^{(k)}$ is the fraction infected in season $k-1$, these individuals have relative susceptibility $\delta_k$ in season $k$, and

$$R_e^{(k)} = \tau_k\bigl(\delta_k p^{(k)} + (1 - p^{(k)})\bigr).$$

The season's final size $z^{(k)}$ solves the multi-group final-size equations (unique positive solution iff $R_e^{(k)} > 1$, otherwise $z^{(k)} = 0$), and $p^{(k+1)} = z^{(k)}$. In general the state is the vector $\mathbf p^{(k)}$ of fractions by years since last infection with immunity levels $\boldsymbol\iota^{(k)}$.

**Theorem.**
1. If $(\delta, \tau)$ has a continuous positive density on $[0,1) \times [0,\infty)$ and an atom at $\delta = 1$ (no immunity) with positive probability, the chain $(\mathbf p^{(k)}, \boldsymbol\iota^{(k)})$ is recurrent, aperiodic and converges to a stationary distribution $\bar\pi$.
2. In the one-season-memory model: if $p^{(k)} = 0$, $(z^{(k)}, R_e^{(k)})$ lies on the curve $1 - z = e^{-R_e z}$ (with $z = 0$ for $R_e \le 1$) and $R_e^{(k)}$ has density $q_R(y) = \int_0^1 q(x, y)\, dx$. The transition probabilities to the no-epidemic state are

$$\mathbb P(p^{(k+1)} = 0 \mid p^{(k)} = 0) = \mathbb P(\tau \le 1), \qquad \mathbb P(p^{(k+1)} = 0 \mid p^{(k)} = p) = \mathbb P\bigl(\tau(\delta p + 1 - p) \le 1\bigr).$$

3. If $q$ has support in $(0,1) \times (\tau_m, \tau_M)$ with $\tau_m < 1 < \tau_M$ and positive $\tau$-marginal there, the chain $p^{(k)}$ is recurrent, aperiodic and converges to a stationary law consisting of an atom at $0$ (seasons without an epidemic) and an absolutely continuous part.

## Expansion

Given the immunity state, a season's outcome is a deterministic function of the fresh pair $(\delta_k, \tau_k)$, so the immunity state is a Markov chain driven by i.i.d. noise. Positivity of the densities and the possibility of complete loss of immunity make every region reachable and give a regeneration (the no-immunity state), which yields recurrence, aperiodicity and convergence. Seasons with $R_e \le 1$ produce no epidemic and a population with no recent infections, which is why the stationary law has an atom at $0$. The model links observed early-season $R_e$ to the eventual final size and to next season's risk.

## Sources

- T. Britton, A. Pugliese, "A multi-season epidemic model with random genetic drift and transmissibility", *Journal of Mathematical Biology* 91(6) (2025), 80, Propositions 2.1, 3.1, 3.2 and 3.3, <https://doi.org/10.1007/s00285-025-02308-8> (preprint arXiv:2505.17933).
