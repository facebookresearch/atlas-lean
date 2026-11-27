# Barrier certificates for invalidating biological models

**Setting.** A candidate model is $\dot x = f(x, p)$ with state $x \in X \subseteq \mathbb R^n$ and unknown parameters $p \in P \subseteq \mathbb R^m$. Experimental data are summarized as sets: at time $t_1$ the state lies in $X_1$ and at time $t_\ell > t_1$ in $X_\ell$ (measurement uncertainty and unknown initial conditions are absorbed into these sets). The model and parameter set are *invalidated* by the data if no $p \in P$ admits a trajectory with $x(t_1) \in X_1$, $x(t_\ell) \in X_\ell$ and $x(t) \in X$ for $t \in [t_1, t_\ell]$.

**Theorem (barrier certificate).** Suppose there is a function $B(x, p, t)$, differentiable in $x$ and $t$, such that

$$B(x_\ell, p, t_\ell) - B(x_1, p, t_1) > 0 \qquad \text{for all } x_1 \in X_1,\ x_\ell \in X_\ell,\ p \in P,$$

$$\frac{\partial B}{\partial x}(x, p, t)\, f(x, p) + \frac{\partial B}{\partial t}(x, p, t) \le 0 \qquad \text{for all } (x, p, t) \in X \times P \times [t_1, t_\ell].$$

Then the model is invalidated by the data.

**Computation.** If $f$ is polynomial and $X, P, X_1, X_\ell$ are semialgebraic, $\{\,z : g_k(z) \ge 0\,\}$, restrict $B$ to polynomials $\sum_j c_j b_j(x, p, t)$ and replace each nonnegativity condition by a sum-of-squares condition after adjoining the set constraints with SOS multipliers (an $\varepsilon > 0$ is subtracted to enforce strict positivity). Feasibility in the coefficients $c_j$ is then a semidefinite program; any feasible solution is a certificate. Reparametrizing time as $\mu = e^{-\lambda t}$ can lower the degree of certificate needed. For a discrete-time polynomial model $x_{k+1} = f(x_k, p)$, the composed map $x_\ell = F_\ell(x_1, p)$ is polynomial and invalidation is emptiness of

$$\{(x_1, p) : x_1 \in X_1,\ p \in P,\ F_\ell(x_1, p) \in X_\ell\},$$

certified by a Positivstellensatz identity found by SOS programming.

## Expansion

Along any trajectory, the derivative condition makes $t \mapsto B(x(t), p, t)$ nonincreasing, so $B(x(t_\ell), p, t_\ell) \le B(x(t_1), p, t_1)$, contradicting the first condition if the trajectory started in $X_1$ and ended in $X_\ell$. Thus no parameter in $P$ is consistent with the data. The certificate is a proof, not a failed search: unlike simulation-based parameter sweeps, which can never exclude all parameters in a continuum, a feasible SOS program settles invalidation, and checking a given certificate takes polynomial time. The search itself is a relaxation: failure to find a certificate of a given degree does not validate the model. Examples include an enzymatic reaction with product degradation, invalidated using product measurements alone with a degree-4 polynomial certificate (degree 3 after time reparametrization), and a logistic map invalidated by data generated from a delayed logistic equation.

## Sources

- J. Anderson, A. Papachristodoulou, "On validation and invalidation of biological models", BMC Bioinformatics (2009), Methods, Theorem 1 (barrier certificate), SOS formulation (Eqs. 8–13) with time reparametrization, discrete-time case and Positivstellensatz formulation; Results, enzymatic reaction (Eq. 15) and population growth (Eq. 23) examples. <https://doi.org/10.1186/1471-2105-10-132> (PMC2704209).
