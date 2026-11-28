# TMRCA and the bottleneck at the MRCA of a stationary CB population

Let $\psi$ be a sub-critical branching mechanism

$$\psi(\lambda) = \alpha\lambda + \beta\lambda^2 + \int_{(0,\infty)} \pi(d\ell)\,\big(e^{-\lambda\ell} - 1 + \lambda\ell\big), \qquad \lambda \ge 0,$$

with $\alpha = \psi'(0) > 0$, $\beta \ge 0$, $\pi$ a Radon measure on $(0,\infty)$ with $\int (\ell\wedge\ell^2)\,\pi(d\ell) < \infty$, and either $\beta > 0$ or $\pi((0,1)) = \infty$. Assume

$$\text{(A1)}\ \int_1^\infty \frac{dv}{\psi(v)} < \infty, \qquad \text{(A2)}\ \int_1^\infty \ell\log\ell\,\pi(d\ell) < \infty.$$

Let $u(\lambda,t)$ solve $u(\lambda,t) + \int_0^t \psi(u(\lambda,s))\,ds = \lambda$ (so a CB $Y$ started at $x$ has $\mathbb E_x[e^{-\lambda Y_t}] = e^{-x u(\lambda,t)}$), let $c(t)$ be defined by $\int_{c(t)}^\infty dv/\psi(v) = t$ (so $\mathbb P_x(Y_t = 0) = e^{-x c(t)}$), and put $\tilde\psi'(\lambda) = \psi'(\lambda) - \psi'(0)$.

Let $(Z_t, t\in\mathbb R)$ be the **stationary CB with immigration**: a CB with branching mechanism $\psi$ and immigration $\tilde\psi'$ in its invariant law, built as a Poisson superposition of independent CB "clans" $Y^i$ born at times $t_i$. Under (A2), $Z_t < \infty$ a.s. and $\mathbb E[Z_t] = \psi''(0+)/\psi'(0)$. At time $0$ write $Z = Z_0$, let $-A$ be the birth time of the oldest clan alive at time $0$ (so $A$ is the **TMRCA** of the population at time $0$), let $Z^O$ be that clan's size at time $0$, $Z^I = Z - Z^O$, and $Z^A = Z_{(-A)-}$ the population size just before the MRCA.

**Theorem.** For $\lambda,\gamma,\eta \ge 0$ and $t \ge 0$,

$$\mathbb E\big[e^{-\lambda Z^A - \gamma Z^I - \eta Z^O};\ A\in dt\big] = dt\,\big(\tilde\psi'(c(t)) - \tilde\psi'(u(\eta,t))\big)\exp\Big(-\int_0^t \tilde\psi'(u(\gamma,s))\,ds - \int_0^\infty \tilde\psi'(u(\lambda + c(t),s))\,ds\Big).$$

Consequently:

1. $\mathbb P(A \le t) = \mathbb E[e^{-c(t) Z}] = \exp\big(-\int_t^\infty \tilde\psi'(c(s))\,ds\big)$, and $A$ has density $f_A(t) = \tilde\psi'(c(t))\exp\big(-\int_t^\infty\tilde\psi'(c(s))\,ds\big)\mathbf 1_{\{t>0\}}$.
2. Conditionally on $A$, the variables $Z^A$, $Z^I$, $Z^O$ are independent, and $\mathbb E[Z^A\mid A = t] = \tilde\psi'(c(t))/\psi(c(t))$.
3. (**Bottleneck at the MRCA.**) $\mathbb P(Z^A \le z\mid A = t) \ge \mathbb P(Z \le z)$ for all $z,t\ge 0$. Hence $Z^A$ is stochastically smaller than the current size $Z$, and $\mathbb E[Z^A\mid A] \le \mathbb E[Z]$ a.s.

## Depends on

- [Kingman's coalescent and the TMRCA](../tmrca.md)

## Expansion

The clans form a Poisson point measure with intensity $dt\,\tilde\psi'$-driven immigration times the CB excursion measure. The event $\{A\in dt\}$ means that one clan born at $-t$ survives to time $0$ while every older clan is extinct by time $0$; clans younger than $t$ contribute $Z^I$. The exclusion formula for Poisson measures gives the exponential factor, and the survival intensity of the oldest clan gives the prefactor. Conditionally on $A = t$, $Z^A$ is the stationary size $Z_{-t}$ conditioned on all of its descendants dying out within time $t$; that is the size-biasing by $e^{-c(t) Z}$ in $\mathbb E[e^{-\lambda Z^A}\mid A=t] = \mathbb E[e^{-(\lambda + c(t))Z}]/\mathbb E[e^{-c(t)Z}]$. Tilting by a decreasing function lowers the law stochastically, which is the bottleneck.

## Sources

- Yu-Ting Chen, Jean-François Delmas, "Smaller population size at the MRCA time for stationary branching processes", *The Annals of Probability* 40 (2012), 2034–2068, <https://doi.org/10.1214/11-AOP668>; preprint arXiv:1009.0814, <https://doi.org/10.48550/arXiv.1009.0814>. Numbering of the arXiv version: Section 2 (branching mechanism, (A1)), Section 3 ((A2), Corollary 3.9), Theorem 4.1, Corollaries 4.2–4.4, Proposition 4.5.
