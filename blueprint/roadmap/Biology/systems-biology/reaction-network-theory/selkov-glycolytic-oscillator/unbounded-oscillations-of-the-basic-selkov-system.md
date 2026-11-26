# Unbounded oscillations of the basic Selkov system

Let $\gamma > 1$ (cooperativity) and $\alpha > 0$. The **basic Selkov system** for the dimensionless substrate $x \ge 0$ and product $y \ge 0$ concentrations is

$$\frac{dx}{d\tau} = 1 - x y^{\gamma}, \qquad \frac{dy}{d\tau} = \alpha\, y\,\bigl(x y^{\gamma-1} - 1\bigr).$$

Solutions with positive initial data stay positive and exist for all $\tau \ge 0$, since $\frac{d}{d\tau}(\alpha x + y) = \alpha(1-y)$.

**Known properties.** For every $\alpha$:
1. the unique positive steady state is $P_0 = (1,1)$;
2. for $0 < \alpha < \alpha_0 := 1/(\gamma-1)$, $P_0$ is asymptotically stable and there are no periodic solutions;
3. at $\alpha = \alpha_0$ a generic supercritical Hopf bifurcation occurs;
4. there are $x_0, y_0 > 0$ such that any solution with $x(t) \ge x_0$ and $y(t) \le y_0$ at some time is eventually monotone with $x \to \infty$ and $y \to 0$.

**Theorem.** There is a unique $\alpha_1 > \alpha_0$ such that:
1. for $\alpha = \alpha_1$ there are solutions with $\liminf_{t\to\infty} x = \liminf_{t\to\infty} y = 0$ and $\limsup_{t\to\infty} x = \limsup_{t\to\infty} y = \infty$ (unbounded oscillations);
2. for $\alpha_0 < \alpha < \alpha_1$ there is a unique periodic solution, and it is asymptotically stable;
3. for $\alpha > \alpha_1$ every solution other than $P_0$ is unbounded and eventually monotone as in property 4;
4. as $\alpha \uparrow \alpha_1$ the diameter of the image of the periodic solution tends to infinity.

## Proof depends on

- [Poincaré–Bendixson theorem](../../../../Dynamics/low-dimensional-dynamics/poincar-bendixson-theorem/poincare-bendixson.md)

## Expansion

After a Poincaré compactification (with one point at infinity blown up) the boundary carries steady states $P_1,\dots,P_4$; $P_1$ and $P_3$ each have a unique one-dimensional centre manifold, with the flow leaving $P_1$ and entering $P_3$. For $\alpha > \alpha_0$ exactly one of three cases holds: the two centre manifolds coincide (a heteroclinic cycle at infinity attracts every solution above it), they differ and a unique periodic orbit exists, or they differ and almost every solution escapes to $P_4$. Let $\xi_1(\alpha)$, $\xi_2(\alpha)$ be where the centre manifolds of $P_1$ and $P_3$ meet the segment $\{y = 1,\ 0 < x \le 1\}$. Both are continuous in $\alpha$. For $\alpha$ near $\alpha_0$ the stable limit cycle forces $\xi_1 - \xi_2 > 0$; for large $\alpha$ a geometric singular perturbation argument in the variables $\bar y = x^{-1/\gamma} y^{1/\gamma}$, $\bar z = x^{-1/\gamma} y^{-(\gamma-1)/\gamma}$ with $\epsilon = \alpha^{-1}$ gives a connection from $P_0$ to $P_3$, so $\xi_2 = 1 > \xi_1$. The intermediate value theorem gives $\alpha_1$; a monotonicity comparison of the centre-manifold expansions shows $\xi_1 - \xi_2$ is strictly decreasing, so $\alpha_1$ is unique. Poincaré–Bendixson and stability of all periodic orbits give the remaining statements. The unbounded solutions cast doubt on the model's biological realism, in contrast to the bounded Goldbeter–Lefever model.

## Sources

- P. Brechmann, A. D. Rendall, "Unbounded solutions of models for glycolysis", Journal of Mathematical Biology (2021), Eqs. (9)–(10), Proposition 1, Theorem 1, Lemmas 1–4 and Theorem 2, <https://doi.org/10.1007/s00285-021-01560-y>, PMCID PMC7819955.
- E. E. Selkov, "Self-oscillations in glycolysis. I. A simple kinetic model", European Journal of Biochemistry (1968), <https://doi.org/10.1111/j.1432-1033.1968.tb00175.x>.
