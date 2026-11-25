# Predictable quadratic variation of Dynkin martingales for bounded-rate jump processes

Let $E$ be a compact metric space and $\mu$ a kernel on $E$ with $x\mapsto\mu(x,\cdot)$ weakly continuous and $\lambda=\sup_x\mu(x,E)<\infty$, and let

$$Bf(x)=\int_E\bigl(f(y)-f(x)\bigr)\,\mu(x,dy),\qquad f\in C(E),$$

be the bounded generator of the [bounded-rate jump Markov process](../../markov-chains/markov-processes-from-transition-semigroups/bounded-rate-jump-markov-process-on-a-compact-sp.md) $X$, a càdlàg process that is Markov with semigroup $e^{tB}$ with respect to a filtration $(\mathcal F_t)$. For $f\in C(E)$ put

$$M^f_t=f(X_t)-f(X_0)-\int_0^tBf(X_s)\,ds,\qquad\Gamma(f)(x)=B(f^2)(x)-2f(x)\,Bf(x)=\int_E\bigl(f(y)-f(x)\bigr)^2\mu(x,dy).$$

Then $M^f$ is a square-integrable martingale; $(M^f_t)^2-\int_0^t\Gamma(f)(X_s)\,ds$ is a martingale; $0\le\Gamma(f)\le4\lambda\|f\|_\infty^2$; and for every bounded stopping time $\tau$ and $\delta>0$,

$$\mathbb E\bigl[(M^f_{\tau+\delta}-M^f_\tau)^2\bigr]\le4\lambda\|f\|_\infty^2\,\delta .$$

Since $B$ is bounded on $C(E)$, $f^2$ lies in its domain for every $f\in C(E)$. The result applies to finite products of such processes moving independently, whose generator has the summed kernel; for $N$ coordinates the total rate is at most $N\lambda$, as for $N$-particle systems.

## Depends on

- [Bounded-rate jump Markov process on a compact space by uniformization](../../markov-chains/markov-processes-from-transition-semigroups/bounded-rate-jump-markov-process-on-a-compact-sp.md)

## Proof depends on

- [Optional stopping for right-continuous martingales](optional-stopping-right-continuous.md)

## Expansion

A full proof derives the Dynkin martingale from the semigroup ($\frac d{dt}e^{tB}f=e^{tB}Bf$ in norm), applies it to $f^2$, and expands $(M^f_t)^2$ to identify the compensator $\int\Gamma(f)(X_s)\,ds$. The increment bound follows from optional stopping at $\tau$ and $\tau+\delta$ for the martingales $M^f$ and $(M^f)^2-\int\Gamma(f)(X_s)\,ds$; this needs optional stopping for right-continuous martingales, not only continuous ones.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, <https://doi.org/10.1002/9780470316658>, martingales associated with Markov jump processes (topic).
