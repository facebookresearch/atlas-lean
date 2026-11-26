# Positivity-preserving nonstandard scheme for the saturating SIS model

**Setting.** For the SIS model with saturating contact rate,

$$\frac{dS}{dt} = \Lambda - \frac{\beta S I}{h(N)} - \mu S + \gamma I, \qquad \frac{dI}{dt} = \frac{\beta S I}{h(N)} - (\mu + \delta + \gamma) I, \qquad h(N) = 1 + bN + \sqrt{1 + 2bN},$$

consider the first-order nonstandard finite difference (NSFD) schemes, in Mickens' framework, with step size $\Delta t > 0$ and a denominator function $\phi(\Delta t) = \Delta t + O(\Delta t^2)$, $\phi > 0$:

$$\frac{S_{k+1} - S_k}{\phi(\Delta t)} = \Lambda - \frac{\beta S_{k+1} I_k}{h(N_k)} - \mu S_{k+1} + \gamma I_k,$$

$$\frac{I_{k+1} - I_k}{\phi(\Delta t)} = \frac{\beta S_{k+1} I_k}{h(N_k)} - (\mu + \delta) I_{k+1} - \gamma I_k,$$

with $N_k = S_k + I_k$. The loss terms are discretized implicitly (nonlocally) and the recovery transfer $\gamma I$ explicitly.

**Theorem.** If the denominator function satisfies

$$\phi(\Delta t) < \frac{1}{\gamma} \quad \text{for all } \Delta t > 0,$$

then for arbitrary initial data $S_0, I_0 \ge 0$ and every step size the scheme generates $S_k, I_k \ge 0$ for all $k \ge 0$; the scheme is dynamically consistent with the positivity of the continuous model.

## Depends on

- [Global stability of the SIS model with saturating contact rate](global-stability-of-the-sis-model-with-saturating-contact-rate.md)

## Expansion

The scheme is explicit after rearrangement:

$$S_{k+1} = \frac{S_k + \phi\Lambda + \phi\gamma I_k}{1 + \phi\beta I_k/h(N_k) + \phi\mu}, \qquad I_{k+1} = \frac{(1 - \phi\gamma) I_k + \phi\beta S_{k+1} I_k / h(N_k)}{1 + \phi(\mu + \delta)}.$$

The first quotient is nonnegative whenever $S_k, I_k \ge 0$; the second is nonnegative exactly when $1 - \phi\gamma \ge 0$, which the condition on $\phi$ guarantees for every step size, e.g. $\phi(\Delta t) = (1 - e^{-\gamma\Delta t})/\gamma$. Second-order members of the family combine a weighted nonlocal approximation of the right-hand side with renormalized denominator functions.

## Sources

- M. T. Hoang, "A Mathematical Study of an SIS Epidemic Model: Global Asymptotic Stability Analysis and Construction of Nonstandard Finite Difference Schemes", arXiv:2609.29567 (2026), Section 3, schemes (NSFD1st), condition (NSFD4), Theorem 3.1 and Theorems 3.2–3.3 for the second-order family, <https://doi.org/10.48550/arXiv.2609.29567>.
