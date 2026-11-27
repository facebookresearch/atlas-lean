# Quasi-potential from an orthogonal decomposition of the drift

**Setting.** For a Langevin equation with additive noise

$$dx = f(x)\,dt + \sigma I_n\,dW_t, \qquad \sigma \to 0,$$

the Freidlin–Wentzell action of a path $\varphi$ on $[0,T]$ is $S(\varphi) = \sigma^{-2}\int_0^T|\dot\varphi - f(\varphi)|^2dt$, and the **quasi-potential** relative to a stable fixed point $a$ is $Q_a(x) = \inf\{S(\varphi) : \varphi(0) = a,\ \varphi(T) = x,\ T > 0\}$, so that the stationary density behaves like $e^{-Q_a/2}$ in the basin of $a$ (with this normalisation of $S$; for $dx = -x\,dt + \sigma\,dW_t$ the stationary law is $\propto e^{-x^2/\sigma^2}$ and $Q_0(x) = 2x^2/\sigma^2$) (Waddington-type landscapes of cell fate).

**Decomposition.** Write $f = -\nabla U + f_U$. The decomposition is **sub-orthogonal** if $\nabla U\cdot f_U \le 0$ and **orthogonal** if $\nabla U\cdot f_U = 0$. A sub-orthogonal decomposition with $U \ge 0$ makes $U$ a Lyapunov function, since $\nabla U\cdot f = -|\nabla U|^2 + \nabla U\cdot f_U \le 0$.

**Proposition.** If the decomposition is orthogonal, then within the basin of $a$

$$Q_a(x) = \frac{4}{\sigma^2}\big(U(x) - U(a)\big),$$

the minimum-action path being the time reversal of $\dot\varphi = \nabla U + f_U$.

**Lemma (linear systems).** Let $f(x) = Ax$ with $A$ stable and $U(x) = \tfrac12x^\top Px$, $P = P^\top$. If $P$ maximizes $\mathrm{tr}(P)$ subject to the linear matrix inequality $P(A + P) \preceq 0$, then

$$PA + A^\top P + 2P^2 = 0,$$

i.e. $\nabla U\cdot f_U = 0$: the optimization returns the exact orthogonal decomposition, hence the exact quasi-potential. For polynomial $f$ the same program, with the matrix inequality replaced by sum-of-squares constraints, yields sub-orthogonal decompositions that can be improved iteratively.

## Proof sketch

Expanding $|\dot\varphi + \nabla U - f_U|^2 = |\dot\varphi - \nabla U - f_U|^2 + 4\nabla U\cdot\dot\varphi - 4\nabla U\cdot f_U$ and using orthogonality, the action is at least $4\sigma^{-2}\int\nabla U\cdot\dot\varphi = 4\sigma^{-2}(U(x) - U(a))$, with equality along the reversed path. In the linear case the stationary covariance $\Sigma$ solves the Lyapunov equation $A\Sigma + \Sigma A^\top + \sigma^2I = 0$, and the orthogonal $P$ is a scaled $\Sigma^{-1}$; the maximal solution of the Riccati equation (Gohberg–Lancaster–Rodman) shows that the trace-maximizing feasible $P$ attains it. Sum-of-squares programming makes the construction tractable beyond linear systems.

## Sources

- R. D. Brackston, A. Wynn and M. P. H. Stumpf, "Construction of quasipotentials for stochastic dynamical systems: An optimization approach", *Physical Review E* 98 (2018), 022136, <https://doi.org/10.1103/physreve.98.022136>. Preprint version: arXiv:1805.07273 (2018), Section 2 (sub-orthogonal decomposition and quasi-potential), Sections 3–5, Lemma 1 (Appendix A) and Lemma 2 (Appendix B), <https://doi.org/10.48550/arXiv.1805.07273>.
