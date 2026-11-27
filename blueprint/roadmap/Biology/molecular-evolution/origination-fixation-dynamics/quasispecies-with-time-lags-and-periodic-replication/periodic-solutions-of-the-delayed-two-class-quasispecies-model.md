# Periodic solutions of the delayed two-class quasispecies model with periodic replication

**Model.** A population of replicators is split into the master sequence (fraction $x_0$) and a pool of mutants ($x_1$). Replication takes time, introducing lags $r_0, r_1 \ge 0$, and replication rates $f_0(t), f_1(t)$ are positive continuous $T$-periodic functions (for example seasonal or therapy-driven forcing). With forward mutation probability $\mu \in [0,1]$ (master to mutant) and backward probability $\xi \in [0,1]$ (mutant to master), and the constant-population dilution $\Phi(t) = f_0(t)x_0(t - r_0) + f_1(t)x_1(t - r_1)$,

$$\dot x_0 = f_0(1-\mu)\,x_0(t - r_0) + f_1\,\xi\,x_1(t - r_1) - x_0(t)\,\Phi(t),$$

$$\dot x_1 = f_0\,\mu\,x_0(t - r_0) + f_1(1 - \xi)\,x_1(t - r_1) - x_1(t)\,\Phi(t).$$

For continuous positive initial histories with $x_0 + x_1 = 1$ at the initial time, the simplex $\Sigma = \{x_0 + x_1 = 1,\ x_0, x_1 > 0\}$ is invariant, as it is for the general $(n+1)$-class model $\dot x_i = \sum_j f_j Q_{ji} x_j(t - r_j) - x_i(t)\sum_j f_j x_j(t - r_j)$; and any positive $T$-periodic solution in $(0,1)^{n+1}$ automatically lies in the simplex.

**Theorem.** Assume $\mu, \xi \in (0,1)$ (both mutation directions present, neither certain).

1. *Existence.* If $\xi \ne 1 - \mu$, the delayed system has at least one non-trivial positive $T$-periodic solution in $\Sigma$, and it satisfies

    $$\min\{1-\mu, \xi\} \le x_0(t) \le \max\{1-\mu, \xi\}, \qquad \min\{1-\xi, \mu\} \le x_1(t) \le \max\{1-\xi, \mu\}.$$

2. *A priori bounds.* Every positive $T$-periodic solution in $(0,1)^2$ lies in $\Sigma$ and:
    - if $1 - \mu > \xi$, then $\xi < x_0(t) < 1 - \mu$ and $\mu < x_1(t) < 1 - \xi$ for all $t$;
    - if $1 - \mu < \xi$, then $1 - \mu < x_0(t) < \xi$ and $1 - \xi < x_1(t) < \mu$ for all $t$;
    - if $1 - \mu = \xi$, the solution is constant, $x_0 \equiv \xi$, $x_1 \equiv 1 - \xi$.

## Expansion

On the invariant simplex the system reduces to a single scalar delay equation for $x_0$. The interval $[\min\{1-\mu,\xi\}, \max\{1-\mu,\xi\}]$ is forward invariant for the reduced equation, since $\dot x_0 = \Phi(t)\big(w(t) - x_0(t)\big)$ where $w = \big(f_0(1-\mu)x_0(t-r_0) + f_1\xi x_1(t-r_1)\big)/\Phi$ is a weighted average of $1 - \mu$ and $\xi$, so $x_0$ is always driven toward that interval. The paper rewrites the periodic boundary-value problem as a fixed-point problem for a completely continuous operator and applies Leray–Schauder degree on a box given by these bounds to obtain a periodic orbit, and the strict bounds follow from comparison at points where $x_0$ attains its extrema. When $1 - \mu = \xi$, master and mutant pools produce masters at the same rate, so the composition is frozen at $\xi$ regardless of lags and forcing.

## Sources

- Edward A. Turner, Francisco Crespo, Josep Sardanyés and Nolbert Morales, "Quasispecies dynamics with time lags and periodic fluctuations in replication", *Journal of Mathematical Biology* 91 (2025), 13, <https://doi.org/10.1007/s00285-025-02239-4>. Numbering as in the preprint arXiv:2412.10475v1, <https://arxiv.org/abs/2412.10475v1>: Propositions 1–3 (Section 2, general model) and Theorems 2 and 3 (Section 3, periodic fitness with backward mutation).
