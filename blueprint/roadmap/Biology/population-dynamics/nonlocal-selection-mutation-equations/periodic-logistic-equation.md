# Periodic logistic equation

Let $a:\mathbb R \to \mathbb R$ be continuous and $T$-periodic, with mean $\bar a = \frac1T\int_0^T a(s)\,ds$. Consider

$$\frac{d\varrho}{dt} = \varrho(t)\bigl(a(t) - \varrho(t)\bigr).$$

**Theorem.** If $\bar a > 0$, the equation has a unique positive $T$-periodic solution

$$\tilde\varrho(t) = \frac{1 - \exp\!\left(-\int_0^T a(s)\,ds\right)}{\int_t^{t+T}\exp\!\left(-\int_s^{t+T} a(\theta)\,d\theta\right)ds},$$

and every solution with $\varrho(0) > 0$ satisfies $|\varrho(t) - \tilde\varrho(t)| \to 0$ as $t\to\infty$. If $\bar a \le 0$, every non-negative solution tends to $0$. The time average of the periodic solution equals the mean growth rate: $\frac1T\int_0^T\tilde\varrho(t)\,dt = \bar a$.

## Depends on

This node has no prerequisites.

## Proof depends on

Its proof is that of the source below, as the Expansion describes.

## Expansion

For a positive solution, $\kappa = 1/\varrho$ satisfies the linear equation $\kappa' = -a(t)\kappa + 1$, so with an integrating factor $\kappa(t+T) = e^{-\int_t^{t+T}a}\,\kappa(t) + \int_t^{t+T}e^{-\int_s^{t+T}a}\,ds$. Periodicity of $a$ gives $\int_t^{t+T}a = T\bar a$; the affine map $\kappa \mapsto e^{-T\bar a}\kappa + c(t)$ is a contraction exactly when $\bar a > 0$, and its unique fixed point is $\kappa(t) = c(t)/(1 - e^{-T\bar a})$, which is the reciprocal of the displayed formula. Iterating the contraction gives convergence of every positive solution; when $\bar a \le 0$ the iterates of $\kappa$ grow without bound, so $\varrho \to 0$. Integrating $\varrho'/\varrho = a - \varrho$ over one period of the periodic solution gives $0 = T\bar a - \int_0^T\tilde\varrho$.

## Sources

- S. Figueroa Iglesias and S. Mirrahimi, "Long time evolutionary dynamics of phenotypically structured populations in time-periodic environments", SIAM Journal on Mathematical Analysis (2018), Section 1.3 (Proposition 1, Equations 3–4; Proposition 2, Equations 5–8; Theorem 4, Equations 9–13), Section 1.4 (Equations 14–16) and Section 2, <https://doi.org/10.1137/18M1175185>.
