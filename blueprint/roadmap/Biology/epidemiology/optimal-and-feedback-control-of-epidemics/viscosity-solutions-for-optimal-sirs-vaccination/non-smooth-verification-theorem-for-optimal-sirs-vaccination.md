# Non-smooth verification theorem for optimal SIRS vaccination

Let $\beta, \gamma, \eta > 0$ (infection, recovery and immunity-loss rates) and let the vaccination rate $u(\cdot)$ take values in $U = [0,\overline{U}]$. Normalized susceptible and infected fractions evolve by the SIRS dynamics with $R = 1 - S - I$,

$$S' = -\beta S I - u S + \eta(1 - S - I), \qquad I' = \beta S I - \gamma I,$$

on $\mathcal{M} = \{(s,i) \in (0,1)^2 : s + i < 1\}$, which is invariant. A social planner minimizes $\int_0^\infty e^{-rt} C(S(t), I(t), u(t))\,dt$ with discount $r > 0$, where the running cost $C$ is continuous, bounded, strictly convex in $u$, Lipschitz and uniformly semiconcave in $(s,i)$. Let $V$ be the value function, $b(x,u) = (-\beta s i - u s + \eta(1-s-i),\ \beta s i - \gamma i)$, and

$$U^\star(s,i,p_s) = \operatorname*{argmin}_{u \in U}\{C(s,i,u) - u\,s\,p_s\},$$

which is single-valued and continuous by strict convexity.

**Theorem.**

1. (HJB) $V$ is well defined, non-negative, bounded and semiconcave on $\mathcal{M}$, and is a viscosity solution of

$$r v(x) = \inf_{u \in U}\big\{\langle b(x,u), Dv(x)\rangle + C(x,u)\big\}, \qquad x \in \mathcal{M}.$$

2. (Verification) Let $v : \mathcal{M} \to \mathbb{R}_+$ be semiconcave, bounded and non-negative. If $v$ is a viscosity subsolution then $v \le V$. If $v$ is a viscosity supersolution and an admissible control $u^\star$ with trajectory $(S^\star, I^\star)$ satisfies $u^\star(t) \in U^\star\big(S^\star(t), I^\star(t), \partial^*_s v(S^\star(t), I^\star(t))\big)$ for a.e. $t$, with $\partial^*_s v$ a reachable partial gradient, then $v = V$ along the starting point and $u^\star$ is optimal.
3. (Feedback and uniqueness) If $(s,i,p_s) \mapsto U^\star(s,i,p_s)$ is locally Lipschitz and $\big(s\,\partial_s \widetilde U^\star\big)^+ \in L^\infty(\mathcal{M})$ for $\widetilde U^\star(s,i) = U^\star(s,i,\partial^+_s v(s,i))$, the closed-loop equation driven by $\widetilde U^\star$ has a regular Lagrangian flow that is optimal for a.e. initial condition, and $V$ is the unique bounded locally semiconcave viscosity solution of the HJB equation.

## Expansion

Semiconcavity of $V$ comes from the semiconcavity and Lipschitz continuity of the cost together with smoothness of the dynamics, as in the stationary version of standard results for exit-free infinite-horizon problems. Semiconcave functions have nonempty convex superdifferentials equal to the convex hull of reachable gradients and are differentiable almost everywhere, so a supersolution can be evaluated along trajectories using reachable gradients; a chain rule along absolutely continuous curves then compares $v$ with the cost of $u^\star$. The subsolution half uses a comparison with every admissible control. Only the $s$-derivative enters the minimization because vaccination acts on the susceptible equation alone, which is why the feedback depends on $\partial_s v$.

## Sources

- Salvatore Federico, Giorgio Ferrari, Maria-Laura Torrente, "Optimal vaccination in a SIRS epidemic model", Economic Theory 77 (2024), 49–74, <https://doi.org/10.1007/s00199-022-01475-9>. Published version of arXiv:2206.03284, cited next; locators there refer to the arXiv version.
- Salvatore Federico, Giorgio Ferrari, Maria-Laura Torrente, "Optimal Vaccination in a SIRS Epidemic Model", arXiv (2022). Section 2 (model and Assumption on $C$), Proposition 2.2, Theorem 3.1, Proposition 3.2, Theorem 3.3, Definition 3.4, Proposition 3.5, Corollary 3.7, Lemma A.1. <https://doi.org/10.48550/arXiv.2206.03284>
