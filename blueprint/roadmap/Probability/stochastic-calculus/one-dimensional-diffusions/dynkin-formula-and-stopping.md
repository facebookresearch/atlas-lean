# Dynkin's formula and optional stopping for diffusions on the unit interval

Let $X$ be a diffusion on $[0, 1]$ solving the martingale problem for $L = \frac12a\,\partial_x^2 + b\,\partial_x$, and let $f$ be twice continuously differentiable on $[0, 1]$, so that $M_t = f(X_t) - f(X_0) - \int_0^tLf(X_s)\,ds$ is a martingale. For a stopping time $T$, Dynkin's formula

$$E_x[f(X_T)] = f(x) + E_x\int_0^TLf(X_s)\,ds$$

holds in each of the following cases, by the optional stopping theorem applied to $M$: (i) $T$ is bounded; (ii) $E_x[T] < \infty$ and $Lf$ is bounded, since then $M_{t \wedge T}$ is dominated by $2\|f\|_\infty + \|Lf\|_\infty T$; (iii) more generally, $M_{t \wedge T}$ is uniformly integrable. Dynkin (1965) states the formula for a Feller process, $f$ in the domain of the generator and $E[T] < \infty$; Øksendal (2003, Theorem 7.4.1) states it for an Itô diffusion, $f$ twice continuously differentiable with compact support and $E^x[T] < \infty$, and hence, for the first exit time of a bounded set with finite mean, for all twice continuously differentiable $f$; the optional stopping theorem used is that for continuous martingales (Karatzas and Shreve 1991, Section 1.3). For $f$ twice continuously differentiable only on $(0, 1)$, such as $\log x$ or a scale function with an infinite endpoint, $f$ coincides on $[1/k, 1 - 1/k]$ with a function smooth on $[0, 1]$, so the formula holds at $T \wedge T_k$, with $T_k$ the exit time from $(1/k, 1 - 1/k)$; letting $k \to \infty$ requires a separate convergence argument (monotone convergence for $Lf$ of one sign, dominated or uniformly integrable convergence of $f(X_{T \wedge T_k})$). This is what the hitting-probability and mean-time identities of Karlin and Taylor (1981, Chapter 15) use: a harmonic $f$ ($Lf = 0$) with bounded values gives $E_x[f(X_T)] = f(x)$ at the absorption time, and a solution of $Lv = -1$ vanishing at the endpoints gives $E_x[T] = v(x)$.

## Depends on

- [Dynkin's formula at a fixed time](../../../Biology/population-genetics/diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/integral-generator.md)

## Proof depends on

- [Optional stopping for right-continuous martingales](../../martingales/stopping-times-and-martingale-problems/optional-stopping-right-continuous.md)

## Expansion

1. The formula at bounded stopping times from the martingale property at fixed times.
2. The extension to $E_x[T] < \infty$ with bounded $Lf$ by dominated convergence of $M_{t \wedge T}$.
3. Localization by the exit times $T_k$ for functions smooth only in the interior, and the passage $k \to \infty$ under each named convergence condition.
4. The two standard applications: fixation probabilities from bounded harmonic functions, and mean absorption times from $Lv = -1$.

## Sources

- E. B. Dynkin, *Markov Processes*, Vols. I and II, Grundlehren der mathematischen Wissenschaften 121–122, Springer, Berlin, 1965.
- B. Øksendal, *Stochastic Differential Equations: An Introduction with Applications*, 6th ed., Springer, Berlin, 2003, Section 7.4, Theorem 7.4.1.
- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer, New York, 1991, Section 1.3 (optional sampling theorem).
- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press, New York, 1981, Chapter 15.
