# Kolmogorov continuous-modification theorem for real-valued processes

Let $(\Omega, P)$ be a probability space and $X = (X_t)_{t \ge 0}$ a real process satisfying Kolmogorov's
condition with exponents $p$ and $q > 1$ and constant $M \ge 0$: for all $s, t \ge 0$ the pair
$(X_s, X_t)$ is measurable and $\mathbb E |X_s - X_t|^p \le M |s - t|^q$ (an expectation in $[0, \infty]$).
Then there is a process $Y = (Y_t)_{t \ge 0}$ such that

1. every $Y_t$ is measurable;
2. every path $t \mapsto Y_t(\omega)$ is continuous;
3. $Y_t = X_t$ almost surely, for each $t \ge 0$ separately;
4. $Y_0(\omega) = X_0(\omega)$ for every $\omega$;
5. for every closed set $S \subseteq \mathbb{R}$ and every $\omega$ such that $X_s(\omega) \in S$ for all
   $s$, also $Y_t(\omega) \in S$ for all $t$.

No indistinguishability of $X$ and $Y$ is claimed.
