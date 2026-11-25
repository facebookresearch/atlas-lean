# Minimum-effort intercept guidance is proportional navigation

Consider a planar engagement linearized about the initial line of sight. Let:
- $y(t)$ be the relative displacement of target and interceptor normal to the line of sight, and $v = \dot y$;
- the target acceleration $a_T$ be constant;
- the interceptor command $u(t)$ act normal to the line of sight, so that $\ddot y = a_T - u$;
- the final time $t_f$ be fixed, with time-to-go $t_{go} = t_f - t$.

The *zero-effort miss* $z(t) = y + v\,t_{go} + \tfrac12 a_T t_{go}^2$ is the miss distance that would result if $u \equiv 0$ from time $t$ on.

**Theorem.** Among square-integrable commands on $[t_0, t_f]$ that achieve zero miss, $y(t_f) = 0$, the command minimizing the effort $\tfrac12 \int_{t_0}^{t_f} u(\tau)^2\,d\tau$ is unique. In feedback form it is

$$
u(t) = \frac{3\,z(t)}{t_{go}^2},
$$

which is proportional navigation with effective navigation ratio $3$. Under this law $z(t)/t_{go}^3$ is constant, so $z(t) \to 0$ and the command stays bounded as $t \to t_f$.

**Proof.** Differentiating gives $\dot z = -t_{go}\,u$. Since $z(t_f) = y(t_f)$, the miss is zero if and only if

$$
\int_{t_0}^{t_f} (t_f - \tau)\,u(\tau)\,d\tau = z(t_0).
$$

By the Cauchy–Schwarz inequality, $z(t_0)^2 \le \int u^2 \cdot \int (t_f - \tau)^2\,d\tau$, with equality exactly when $u$ is proportional to $t_f - \tau$. So the unique minimizer is $u(\tau) = 3 z(t_0)(t_f - \tau)/(t_f - t_0)^3$. Restarting the argument at any later time $t$, the same law gives $u(t) = 3 z(t)/t_{go}^2$. Substituting into $\dot z = -t_{go} u$ gives $\dot z = -3z/t_{go}$, so $z \propto t_{go}^3$.

More generally, for a constant $N > 0$, the error dynamics $\dot z + (N/t_{go}) z = 0$, produced by the command $u = N z/t_{go}^2$, minimize the weighted effort $\tfrac12 \int u^2 / t_{go}^{N-3}\,d\tau$; they give $z \propto t_{go}^N$ and hence zero miss. For $N > 3$ the weight $1/t_{go}^{N-3}$ grows without bound as $t_{go} \to 0$, and the command tends to zero at intercept. Constrained flight, with state, input and terminal constraints, and existence of optimal controls for nonlinear engagement models go beyond this linear-quadratic case.

## Background

- [Six-degree-of-freedom body equations of a rigid motion](six-degree-of-freedom-flight-dynamics-trim-and-l/six-dof-body-equations.md)

## Sources

- S. He and C.-H. Lee, "Optimality of error dynamics in missile guidance problems", *Journal of Guidance, Control, and Dynamics* 41(7):1624–1633, 2018, author manuscript <https://pdfs.semanticscholar.org/57cd/173b0998ea5ad3a67675d85551e769832c55.pdf>:
    - Section I: proportional navigation;
    - Section IV.A: the linearized zero-effort miss $z = y + v t_{go} + \tfrac12 a_T t_{go}^2$ (35) and its dynamics $\dot z = -t_{go} a_M$ (36), the error dynamics $\dot z + (N/t_{go}) z = 0$ (37) with a positive constant $N$, its performance index $\tfrac12 \int u^2/t_{go}^{N-3}$ (38), $N = 3$ as energy minimization and $N > 3$ for zero terminal acceleration command, and the command $a_M = N z/t_{go}^2$ (39). The Cauchy–Schwarz proof is written out here.
