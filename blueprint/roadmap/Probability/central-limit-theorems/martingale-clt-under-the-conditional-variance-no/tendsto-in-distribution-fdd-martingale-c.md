# Finite-dimensional convergence under the conditional-variance normalization

On a probability space, let $(X_{n,k})$ be a square-integrable array whose row partial sums $\sum_{j<k} X_{n,j}$ are martingales for filtrations $(\mathcal F_{n,k})_k$. Let $\iota$ be a linearly ordered time axis, $N_n : \iota \to \mathbb{N}$ monotone with $N_n(s) \le r_n$, and $S_n(s) = \sum_{k < N_n(s)} X_{n,k}$. Suppose that:

- the conditional Lindeberg condition holds on the whole rows: $\sum_{k < r_n} \mathbb{E}[X_{n,k}^2 \mathbf 1\{|X_{n,k}| > \varepsilon\} \mid \mathcal F_{n,k}] \to 0$ in probability for every $\varepsilon > 0$;
- the predictable quadratic variation of the whole row, up to $r_n$, converges in probability to some constant $V$;
- for every time $s$, the predictable quadratic variation up to $N_n(s)$ converges in probability to $A(s)$.

Let $Z$ be a measurable process on a probability space whose finite linear combinations $\sum_{s \in I} c_s Z_s$ are centered Gaussian with variance the nonnegative part of $\sum_{s,u \in I} c_s c_u A(\min(s,u))$. Then for every finite set of times $I$, $(S_n(s))_{s \in I}$ converges in distribution to $(Z_s)_{s \in I}$.

The convergence of the whole-row variation is automatic when the row ends at a time of the axis, $r_n = N_n(s_1)$. It is a convenience of the proof, not a sharp condition.
