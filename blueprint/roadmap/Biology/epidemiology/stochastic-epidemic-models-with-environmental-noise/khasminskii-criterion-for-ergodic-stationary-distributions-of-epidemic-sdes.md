# Khasminskii criterion for ergodic stationary distributions of epidemic SDEs

**Environmental noise.** Perturbing a per-capita rate in a compartmental model by white noise, $d_X\,dt \mapsto d_X\,dt - \nu_X\, dW_X(t)$, turns the equation for compartment $X$ into

$$dX = f_X(\cdot)\,dt + \nu_X X\, dW_X ,$$

with independent standard Brownian motions $W_X$ and noise intensities $\nu_X \ge 0$. For a positive solution, Itô's formula gives $d\ln X = \big(f_X/X - \tfrac12\nu_X^2\big)dt + \nu_X dW_X$, so noise acts like an additional death rate $\nu_X^2/2$: thresholds of the stochastic model involve the corrected rates $\hat d_X = d_X + \nu_X^2/2$. Global existence of a unique positive solution follows by applying the generator $\mathcal{L}$ to $V = \sum_X (X - 1 - \ln X)$ (plus integral terms for delays) and showing $\mathcal{L}V$ is bounded above.

**Khasminskii's criterion.** Let $X(t)$ be a time-homogeneous Markov diffusion in $\mathbb{R}^d$, $dX = b(X)\,dt + \sum_{r} \sigma_r(X)\, dB_r$, with diffusion matrix $\Lambda(x) = (\lambda_{ij}(x))$. Suppose there is a bounded domain $U \subset \mathbb{R}^d$ with regular boundary such that:

- **(A1)** in $U$ and some neighbourhood of it, the diffusion is uniformly nondegenerate: there is $M > 0$ with $\sum_{i,j}\lambda_{ij}(x)\xi_i\xi_j \ge M|\xi|^2$ for all $\xi \in \mathbb{R}^d$;
- **(A2)** there is a nonnegative $C^2$ function $V$ and a constant $C > 0$ with $\mathcal{L}V(x) \le -C$ for all $x \in \mathbb{R}^d \setminus U$.

Then $X$ has a unique stationary distribution $\pi$, it is ergodic, and for every $\pi$-integrable $f$,

$$\lim_{T\to\infty}\frac1T\int_0^T f(X(t))\,dt = \int f\,d\pi \qquad \text{almost surely, for every initial value.}$$

For epidemic SDEs on $\mathbb{R}^d_{>0}$ with diagonal noise $\Lambda = \mathrm{diag}(\nu_1^2 x_1^2, \dots, \nu_d^2 x_d^2)$, (A1) holds on any bounded domain whose closure lies in the open orthant, with $M = \min_{\bar U}\min_i \nu_i^2 x_i^2 > 0$; (A2) is verified with a Lyapunov function combining $-\ln$ of the compartments, weighted to cancel the incidence terms, and a power $(\sum_i x_i)^{\zeta+1}/(\zeta+1)$ controlling large values, under a stochastic threshold condition greater than one.

## Expansion

(A2) makes the process return to $U$ with finite mean hitting time from any compact set (positive recurrence), and (A1) gives local smoothing (strong Feller property and irreducibility) in $U$; together they yield a unique invariant measure and the strong law for time averages. In epidemic applications, the stationary distribution concentrated in the open orthant expresses stochastic persistence: infection fluctuates around a neighbourhood of the deterministic endemic state rather than dying out. Because each noise intensity enters as $\nu^2/2$ added to removal rates, large noise can push the stochastic threshold below one even when the deterministic $\mathcal{R}_0 > 1$, producing noise-induced extinction.

## Sources

- F. A. Rihan, H. J. Alsakaji, "Dynamics of a stochastic delay differential model for COVID-19 infection with asymptomatic infected and interacting people: Case study in the UAE", Results in Physics 28 (2021) 104658, Section 2 (stochastic delay model (2), Theorem 1 with Lyapunov function (4)–(7)) and Section 3 (Lemma 1, corrected rates in (8), Theorem 2 with Lyapunov function (9)), <https://doi.org/10.1016/j.rinp.2021.104658>.
- R. Khasminskii, Stochastic Stability of Differential Equations, 2nd ed., Springer (2012), Chapter 4, <https://doi.org/10.1007/978-3-642-23280-0>.
