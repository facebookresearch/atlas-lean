# Fluid and diffusion limits of a host–vector SIS epidemic with fast vectors

**Model.** A population of $n$ hosts and about $C_0n$ vectors evolves as a continuous-time Markov chain: infected hosts $I_h$ recover (back to susceptible) at rate $\gamma_h^n$; susceptible hosts are infected by infected vectors at rate $\beta_h^n$ per vector-density unit; susceptible vectors are infected by infected hosts at rate $\beta_v^n$; vectors are born susceptible and die at the common rate $\gamma_v^n$. Write $\bar I^n_h=I_h/n$, $\bar I^n_v=I_v/n$, $\bar S^n_v=S_v/n$. Two scalings are considered:

- *Case I* (same time scale): $\beta_h^n\to\beta_h$, $\gamma_h^n\to\gamma_h$, $\beta_v^n\to\beta_v$, $\gamma_v^n\to\gamma_v$;
- *Case II* (fast vectors): host rates as in Case I but $\beta_v^n/\alpha(n)\to\beta_v$, $\gamma_v^n/\alpha(n)\to\gamma_v$ with $\alpha(n)/\sqrt n\to\infty$, $\alpha(n)/n\to0$.

The basic reproduction number is $\mathcal R_0=\sqrt{\dfrac{\beta_h}{\gamma_v}\cdot\dfrac{C_0\beta_v}{\gamma_h}}$.

**Theorem (fluid limit, Case I).** If initial fractions converge in $L^1$, then $(\bar I^n_h,\bar S^n_v,\bar I^n_v)\to(i_h,C_0-i_v,i_v)$ uniformly on compacts in $L^1$, where

$$\dot i_h=\beta_hi_v(1-i_h)-\gamma_hi_h,\qquad \dot i_v=\beta_vi_h(C_0-i_v)-\gamma_vi_v .$$

**Theorem (fluid limit, Case II).** The vector component equilibrates instantaneously: the occupation measure of $(\bar S^n_v,\bar I^n_v)$ concentrates on $\big(\frac{C_0\gamma_v}{\beta_vi_h+\gamma_v},\frac{C_0\beta_vi_h}{\beta_vi_h+\gamma_v}\big)$, and $\bar I^n_h\to i_h$ with

$$\dot i_h=\frac{C_0\beta_h\beta_v\,i_h(1-i_h)}{\beta_vi_h+\gamma_v}-\gamma_hi_h .$$

**Theorem (threshold behaviour).** Both limits have the disease-free equilibrium $0$ and the endemic host level

$$i_h^\ast=\frac{C_0\beta_h\beta_v-\gamma_h\gamma_v}{C_0\beta_h\beta_v+\beta_v\gamma_h}$$

(with $i_v^\ast=\frac{C_0\beta_h\beta_v-\gamma_h\gamma_v}{\beta_h(\beta_v+\gamma_v)}$ in Case I). The disease-free equilibrium is globally asymptotically stable for $\mathcal R_0\le1$ (exponentially for $\mathcal R_0<1$) and unstable for $\mathcal R_0>1$, in which case the endemic equilibrium is globally asymptotically stable from any initial condition with positive infection.

**Theorem (diffusion limits).** Under $\sqrt n$-convergence of the rates, the centred and $\sqrt n$-scaled fluctuations converge to the unique solution of a linear SDE driven by Brownian motions: three-dimensional in Case I and one-dimensional in Case II, the latter with drift linearized along the reduced ODE and diffusion coefficient $\sqrt{\beta_hi_v^\ast(t)(1-i_h(t))+\gamma_hi_h(t)}$, $i_v^\ast(t)=\frac{C_0\beta_vi_h(t)}{\beta_vi_h(t)+\gamma_v}$. In Case I the variances of the limiting fluctuations diverge as $t\to\infty$.

## Expansion

The fluid limits follow from the law of large numbers for density-dependent Markov chains (Kurtz). In Case II vectors turn over $\alpha(n)$ times faster, so averaging over the fast vector dynamics (a stochastic averaging principle) replaces $i_v$ by its quasi-equilibrium given the current host level, reducing the system to a single logistic-type ODE; the condition $\alpha(n)\gg\sqrt n$ also suppresses vector noise at the diffusion scale. Global stability uses the Lyapunov-type monotonicity of these cooperative systems; the endemic levels solve $\beta_hi_v(1-i_h)=\gamma_hi_h$ and $\beta_vi_h(C_0-i_v)=\gamma_vi_v$, and are positive iff $C_0\beta_h\beta_v>\gamma_h\gamma_v$, i.e. $\mathcal R_0>1$.

## Depends on

- [Next-generation basic reproduction number](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Sources

- Xin Liu, Anuj Mubayi, Dominik Reinhold, Liu Zhu, "Approximation Methods for Analyzing Multiscale Stochastic Vector-borne Epidemic Models", arXiv:1806.03778: Section 2 (model, scalings, $\mathcal R_0$), Theorems 3.1 and 3.3 (fluid limits), Theorems 3.2 and 3.4 (equilibria and stability), Theorems 3.6–3.7 (diffusion limits), Lemma 4.2 (diverging variances). <https://doi.org/10.48550/arXiv.1806.03778> Published version: Mathematical Biosciences 309 (2019) 42–65, <https://doi.org/10.1016/j.mbs.2019.01.003>.
