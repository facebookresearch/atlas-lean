# Delay-dependent stability of synchrony in degrade-and-fire oscillators

**Model.** $N$ degrade-and-fire (DF) oscillators with repressor concentrations $x_1,\dots,x_N\ge 0$ share an activator $A\ge 0$:

$$
\dot x_i(t)=-1\ \text{ if } x_i(t)>0,\qquad x_i(t^+)=R+\nu A(t-\tau)\ \text{ if } x_i(t)=0,\qquad
\dot A(t)=m(t)-\beta A(t),\quad m(t)=\frac1N\sum_{i=1}^N x_i(t),
$$

with parameters $R,\beta,\nu>0$, feedback delay $\tau\ge 0$, $\nu<\beta$ and $\tau<R$. Each repressor degrades linearly and is reset by a burst of synthesis ("firing") whose size grows with the delayed activator level; the activator integrates the mean repressor (quorum sensing). The firing order is preserved forever under

$$
\nu<\frac{\beta}{1+\beta R}. \tag{O}
$$

Put $R_\tau=R+\nu\,\frac{1+\beta\tau-e^{\beta\tau}}{\beta^2}$ and $\nu_\tau=\nu e^{\beta\tau}$, and assume

$$
R_\tau>0\quad\text{and}\quad \nu_\tau<\beta . \tag{C}
$$

On the synchronized subspace $x_1=\dots=x_N$ the dynamics reduces to the $N=1$ system, whose return map on the activator value at firing is

$$
F_1(A)=\frac{1}{\beta^2}+\Big(A\big(1-\tfrac{\nu_\tau}{\beta}\big)-\frac{R_\tau}{\beta}-\frac{1}{\beta^2}\Big)e^{-\beta(R_\tau+\nu_\tau A)} .
$$

**Proposition (Fernandez–Tanzi, Proposition 3.1).** Under (C), $F_1$ has a unique globally attracting fixed point $A_{\mathrm{FP}}$ (in $[A_0(\tau),A_\tau]$ with $A_\tau=R_\tau/(\beta-\nu_\tau)$). Assume also (O). Then, for the return map $F_N$ of the $N$-oscillator system and its fixed point $(0,\dots,0,A_{\mathrm{FP}})$ (the fully synchronized periodic orbit):

1. if $\tau=0$, the synchronized orbit is **unstable** in $(\mathbb{R}^+)^N$ for every $N\ge 2$;
2. there is $\tau_0>0$ such that for every $\tau\in(0,\tau_0)$ and every $N\ge 2$, the synchronized orbit is **locally asymptotically stable**.

So an arbitrarily small positive feedback delay converts unstable synchrony into stable synchrony, uniformly in the population size; the conclusion is unaffected by small additive noise in the reset values.

## Proof sketch

The fixed point of $F_1$ follows from $F_1$ mapping $[A_0(\tau),A_\tau]$ strictly into itself while being increasing and concave there. For stability, perturb one oscillator so that it fires slightly before or after the cluster. Without delay, an oscillator firing a little late resets using the activator just after the cluster's firing has started raising $A$ (the derivative of $A$ is positive right after a firing), so it gets a larger reset and drifts further away. With a delay, the reset uses $A(t-\tau)$, sampled before the firing, where $A$ is decreasing; a late oscillator then receives a smaller reset and catches up, giving a contraction of the spread at each return.

## Sources

- Bastien Fernandez and Matteo Tanzi, "Feedback-delay dependence of the stability of cluster periodic orbits in populations of degrade-and-fire oscillators with common activator", *Journal of Mathematical Biology* 90 (2025), 27, <https://doi.org/10.1007/s00285-024-02169-7>. Preprint version: arXiv:2405.07752 (2024), <https://doi.org/10.48550/arXiv.2405.07752>.
