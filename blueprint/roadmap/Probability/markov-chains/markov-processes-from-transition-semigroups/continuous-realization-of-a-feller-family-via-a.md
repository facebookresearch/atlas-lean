# Continuous realization of a Markov family via a moment bound

Let $E=[l,r]$ be a compact real interval and $(K_t)_{t\ge0}$ Markov kernels on $E$ with $K_0(x,\cdot)=\delta_x$ and the Chapman–Kolmogorov equations $K_{s+t}=K_sK_t$. Suppose there are $p>0$, $a>0$ and $C<\infty$ with

$$\int_E|x-y|^p\,K_t(x,dy)\le C\,t^{1+a}\qquad(x\in E,\ 0\le t\le1).$$

Then for every $x\in E$, the canonical process under the [path-space measure](path-measure.md) $P_x$ has a modification with continuous paths; this modification is a Markov process with transition kernels $(K_t)$ for its natural filtration, and it starts at $x$ surely. The statement is for a real interval; a general compact metric state space, such as the circle, is a separate page.

Two probes delimit it. Reflected Brownian motion on $[0,1]$, $K_t(x,\cdot)=$ law of $\varphi(x+B_t)$ with $\varphi$ the $2$-periodic tent map folding $\mathbb R$ onto $[0,1]$, satisfies the bound with $p=4$ and $1+a=2$: $\varphi$ is $1$-Lipschitz and $\varphi(x)=x$ on $[0,1]$, so $\int|x-y|^4K_t(x,dy)\le\mathbb EB_t^4=3t^2$. A two-state continuous-time chain with distinct states $u\ne v$ has $\mathbb E_x|X_t-X_0|^p=|u-v|^pP_x(X_t\ne X_0)$, of order $t$, so the bound fails, as it must for a process with jumps.

## Depends on

- [Path-space measure of a Markov semigroup](path-measure.md)

## Proof depends on

- [Kolmogorov extension theorem](../../foundations/kolmogorov-extension-theorem/kolmogorov-extension.md)

## Expansion

A proof page must establish: the increment bound $\mathbb E_x|X_t-X_s|^p\le C|t-s|^{1+a}$ for $|t-s|\le1$, from the Markov property of the path measure, and a bound by $(r-l)^p|t-s|^{1+a}$ for $|t-s|>1$; a continuous modification on each $[0,N]$ by the Kolmogorov–Chentsov theorem, patched over $N$; the Markov property of the modification, which has the same finite-dimensional laws; the sure start at $x$ after modifying on a null set; and the two probes. The cited Kolmogorov–Chentsov theorem is stated for processes with values in complete (pseudo)metric spaces, so the extension to compact metric $E$ uses the same argument.

## Sources

- R. Degenne, D. Ledvinka, E. Marion and P. Pfaffelhuber, *Formalization of Brownian motion in Lean* (2025), <https://arxiv.org/abs/2511.20118>, Section 2.3 and Theorem 4.20 (Kolmogorov–Chentsov theorem).
