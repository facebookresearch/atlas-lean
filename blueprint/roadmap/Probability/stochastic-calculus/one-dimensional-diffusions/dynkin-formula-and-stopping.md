# Dynkin's formula and optional stopping for diffusions on the unit interval

Let $X$ be a diffusion on $[0, 1]$ solving the martingale problem for $L = \frac12a\,\partial_x^2 + b\,\partial_x$, and let $f$ be twice continuously differentiable on $[0, 1]$, so that $M_t = f(X_t) - f(X_0) - \int_0^tLf(X_s)\,ds$ is a martingale. For a stopping time $T$, Dynkin's formula

$$E_x[f(X_T)] = f(x) + E_x\int_0^TLf(X_s)\,ds$$

holds in each of the following cases, by the optional stopping theorem applied to $M$: (i) $T$ is bounded; (ii) $E_x[T] < \infty$ and $Lf$ is bounded, since then $M_{t \wedge T}$ is dominated by $2\|f\|_\infty + \|Lf\|_\infty T$; (iii) more generally, $M_{t \wedge T}$ is uniformly integrable. Wikipedia (*Dynkin's formula*) states the formula for a Feller process, $f$ in the domain of the generator and $E[T] < \infty$, and for an Itô diffusion and the first exit time of a bounded set with finite mean for all twice continuously differentiable $f$; the conditions of the optional stopping theorem are those of Wikipedia (*Optional stopping theorem*). For $f$ twice continuously differentiable only on $(0, 1)$, such as $\log x$ or a scale function with an infinite endpoint, $f$ coincides on $[1/k, 1 - 1/k]$ with a function smooth on $[0, 1]$, so the formula holds at $T \wedge T_k$, with $T_k$ the exit time from $(1/k, 1 - 1/k)$; letting $k \to \infty$ requires a separate convergence argument (monotone convergence for $Lf$ of one sign, dominated or uniformly integrable convergence of $f(X_{T \wedge T_k})$). This is what the hitting-probability and mean-time identities use: a harmonic $f$ ($Lf = 0$) with bounded values gives $E_x[f(X_T)] = f(x)$ at the absorption time, and a solution of $Lv = -1$ vanishing at the endpoints gives $E_x[T] = v(x)$.

## Depends on

- [Dynkin's formula at a fixed time](../../../Biology/population-genetics/diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/integral-generator.md)

## Expansion

1. The formula at bounded stopping times from the martingale property at fixed times.
2. The extension to $E_x[T] < \infty$ with bounded $Lf$ by dominated convergence of $M_{t \wedge T}$.
3. Localization by the exit times $T_k$ for functions smooth only in the interior, and the passage $k \to \infty$ under each named convergence condition.
4. The two standard applications: fixation probabilities from bounded harmonic functions, and mean absorption times from $Lv = -1$.

## Sources

- Wikipedia, Dynkin's formula, statement and the example of Itô diffusions. <https://en.wikipedia.org/wiki/Dynkin%27s_formula>
- Wikipedia, Optional stopping theorem, statement. <https://en.wikipedia.org/wiki/Optional_stopping_theorem>
