# Extreme first passage times with a positive minimal time and run-and-tumble searchers

**Setting.** Let $\tau_1,\tau_2,\dots$ be i.i.d. first passage times of independent searchers to a target, and $T_N=\min\{\tau_1,\dots,\tau_N\}$ the **extreme (fastest) first passage time**. For a piecewise deterministic Markov process (deterministic motion between random switching events) with bounded speed there is a minimal time $t_0>0$ below which the target cannot be reached, and with positive probability $q$ the searcher reaches it exactly at $t_0$ (moving straight, without switching). Assume

$$
\mathbb P(\tau<t_0)=0,\qquad \mathbb P(\tau=t_0)=q\in[0,1),
$$

and, for some $\alpha,p>0$, as $\varepsilon\to0^+$ either

$$
\text{(i)}\ \ \mathbb P\bigl(t_0<\tau<t_0(1+\varepsilon)\bigr)=(1-q)\alpha\varepsilon^p+o(\varepsilon^p)\quad\text{or}\quad \text{(ii)}\ \ \mathbb P\bigl(t_0<\tau<t_0(1+\varepsilon)\bigr)=(1-q)\alpha\,\varepsilon^p\ln(1/\varepsilon)+o\bigl(\varepsilon^p\ln(1/\varepsilon)\bigr).
$$

**Theorem (Theorem 2).** In distribution, $T_N=t_0\bigl(1+a_N\,\xi_N\,\Sigma_N\bigr)$, where $a_N=(\alpha N)^{-1/p}$ in case (i) and $a_N=(\alpha N\ln N/p)^{-1/p}$ in case (ii), $\xi_N\in\{0,1\}$ is Bernoulli with $\mathbb P(\xi_N=1)=(1-q)^N$, $\Sigma_N\to\mathrm{Weibull}(1,p)$ in distribution (survival function $e^{-x^p}$), and $\xi_N,\Sigma_N$ are independent.

**Theorem (moments, Theorem 4).** If moreover $\mathbb E[T_N]<\infty$ for some $N$, then $\mathbb E[\Sigma_N^m]\to\Gamma(1+m/p)$ and

$$
\mathbb E\bigl[(T_N-t_0)^m\bigr]=(1-q)^N\,(t_0a_N)^m\,\Gamma(1+m/p)+o\bigl((1-q)^N(t_0a_N)^m\bigr),\qquad N\to\infty .
$$

Analogous statements (Theorems 6–7) hold for the $k$-th fastest time with generalized gamma limits.

**Application (run and tumble).** For searchers starting at the center of a ball of radius $L$, moving at speed $v$ and tumbling at rate $\lambda$ (uniform new direction), with $\rho=\lambda L/v$, $t_0=L/v$ and $q=e^{-\rho}$: in 1d, (i) holds with $p=1$; in 2d, (i) holds with $p=1/2$; in 3d, (ii) holds with $p=1$. Consequently

$$
\mathbb E[T_N^{1d}]\approx\frac Lv\Bigl[1+\frac{2(1-e^{-\rho})^{N+1}}{\rho(\rho+1)e^{-\rho}}\frac1N\Bigr],\quad \mathbb E[T_N^{2d}]\approx\frac Lv\Bigl[1+\frac{(1-e^{-\rho})^{N+2}}{(\rho e^{-\rho})^2}\frac1{N^2}\Bigr],\quad \mathbb E[T_N^{3d}]\approx\frac Lv\Bigl[1+\frac{(1-e^{-\rho})^{N+1}}{\rho e^{-\rho}}\frac1{N\ln N}\Bigr].
$$

## Expansion

With probability $1-(1-q)^N$ at least one searcher runs straight to the target and $T_N=t_0$ exactly; otherwise all $N$ times exceed $t_0$ and $T_N$ is the minimum of $N$ i.i.d. variables whose distribution near $t_0$ behaves like $\alpha\varepsilon^p$ (times a logarithm in case (ii)). Classical extreme value theory for minima of variables with a power-law lower tail gives the Weibull limit after rescaling by $a_N$, and uniform integrability (from finiteness of one moment) upgrades convergence in law to convergence of moments. For run and tumble, $\tau\in(t_0,t_0(1+\varepsilon))$ requires a tumble early or late enough that the detour costs at most $\varepsilon t_0$; in 1d this has probability linear in $\varepsilon$, in 2d the angular freedom gives $\varepsilon^{1/2}$, and in 3d a logarithmic correction appears. Diffusion approximations of run-and-tumble motion have no minimal time and predict $T_N\to0$, which is unphysical for large $N$.

## Depends on

- [Weibull distribution](../../../../Probability/distributions/continuous/weibull-distribution/weibull-measure.md)

## Sources

- S. D. Lawley, "Extreme first passage times of piecewise deterministic Markov processes", arXiv:1912.03438 (2019), Section 2 (Proposition 1, Theorems 2, 4, 6–7 and the run-and-tumble summary) and Sections 4–6 (one-, two- and three-dimensional run and tumble), <https://doi.org/10.48550/arXiv.1912.03438>.
