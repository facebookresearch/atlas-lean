# Convergence of ADMM

Let $E$, $F$, $P$ be finite-dimensional real inner product spaces, let $f \colon E \to \mathbb{R}$ and $g \colon F \to \mathbb{R}$ be convex, let $A \colon E \to P$ and $B \colon F \to P$ be linear, $c \in P$ and $\rho > 0$, and write

$$L_\rho(x, z, y) = f(x) + g(z) + \langle y, Ax + Bz - c \rangle + \frac{\rho}{2} \|Ax + Bz - c\|^2.$$

Suppose the unaugmented Lagrangian $L_0$ has a saddle point $(x^\star, z^\star, y^\star)$, i.e. $L_0(x^\star, z^\star, y) \le L_0(x^\star, z^\star, y^\star) \le L_0(x, z, y^\star)$ for all $x, z, y$. If the sequences $(x^k, z^k, y^k)$ follow the ADMM iteration

$$x^{k+1} \in \operatorname*{argmin}_x L_\rho(x, z^k, y^k), \quad z^{k+1} \in \operatorname*{argmin}_z L_\rho(x^{k+1}, z, y^k), \quad y^{k+1} = y^k + \rho\,(Ax^{k+1} + Bz^{k+1} - c),$$

then the residual $Ax^k + Bz^k - c$ tends to $0$ and the objective $f(x^k) + g(z^k)$ tends to the optimal value $p^\star = f(x^\star) + g(z^\star)$.

The source treats closed proper convex extended-real-valued $f$ and $g$ (Assumption 1); real-valued convex functions on finite-dimensional spaces are a special case. The iterates are taken as given minimizers, so nothing is claimed about the solvability of the subproblems. The proof in the source is the Lyapunov argument of Appendix A.

## Sources

- S. Boyd, N. Parikh, E. Chu, B. Peleato and J. Eckstein, "Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers", *Foundations and Trends in Machine Learning* 3(1), 2011, §3.1 (eqs. (3.1)–(3.4)), §3.2 (Assumptions 1 and 2) and Appendix A; https://stanford.edu/~boyd/papers/pdf/admm_distr_stats.pdf.
