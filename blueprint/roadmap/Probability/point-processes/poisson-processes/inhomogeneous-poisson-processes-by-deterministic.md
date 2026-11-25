# Inhomogeneous Poisson processes by a deterministic time change

Let $N$ be a [Poisson process](is-poisson-process.md) of rate $1$, let $\lambda : [0, \infty) \to [0, \infty)$ be locally integrable and let $\Lambda(t) = \int_0^t \lambda(u)\, du$. Then
$M_t = N_{\Lambda(t)}$ has $M_0 = 0$ almost surely, almost surely nondecreasing paths, independent increments over consecutive intervals, and

$$M_t - M_s \sim \mathrm{Poisson}\bigl(\Lambda(t) - \Lambda(s)\bigr) \qquad (0 \le s \le t),$$

because $\Lambda$ is continuous and nondecreasing, so consecutive intervals $[s_i, s_{i+1}]$ are mapped to consecutive intervals
$[\Lambda(s_i), \Lambda(s_{i+1})]$, on which the increments of $N$ are independent and Poisson by the definition of a Poisson process of rate $1$ (a degenerate
interval with $\Lambda(s_i) = \Lambda(s_{i+1})$ gives the increment $0$, which has the law $\mathrm{Poisson}(0)$). So $M$ is the inhomogeneous Poisson process with
intensity $\lambda$. A constant $\lambda \equiv r$ gives the Poisson process of rate $r$; a piecewise-constant $\lambda$, as for a population
bottleneck, gives Poisson increments with means $\sum_k \lambda_k |I_k \cap [s, t]|$.

## Depends on

- [Poisson process](is-poisson-process.md)

## Related topics

- [Independent Poisson increments of the counting process](has-law-count-increments.md)

## Sources

- J. F. C. Kingman, *Poisson Processes*, Oxford University Press (1993) (mapping theorem). The time change is derived above.
