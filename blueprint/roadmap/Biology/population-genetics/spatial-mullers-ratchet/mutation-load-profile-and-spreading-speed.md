# Mutation-load profile and spreading speed of an expanding population

**Model.** Let $u_k(t,x)\ge0$ be the density at position $x\in\mathbb R$ of individuals carrying exactly $k\in\mathbb N_0$ deleterious mutations, $u=(u_k)_k$ with $\|u\|_{\ell_1}=\sum_k u_k$ the total density. With migration rate $m>0$, mutation probability per birth $\mu\in(0,1)$, fitnesses $1=s_0\ge s_1\ge\dots\ge0$ with $s_k\to0$, and polynomial density-dependent birth and death rates $q_+,q_-$ with $\deg q_+<\deg q_-$ (local regulation), the spatial Muller's ratchet limit is

$$\partial_t u_k=\frac m2\,\Delta u_k+q_+(\|u\|_{\ell_1})\big(s_k(1-\mu)u_k+\mathbb 1_{k\ge1}\,s_{k-1}\mu\,u_{k-1}\big)-q_-(\|u\|_{\ell_1})\,u_k,\qquad k\in\mathbb N_0 .$$

For bounded initial data $f\in L_\infty(\mathbb R;\ell_1)$, a.e. continuous with uniformly vanishing tails, there is a unique non-negative global mild solution, each $u_k$ and $\|u\|_{\ell_1}$ being $C^{1,2}$ for $t>0$.

**Monostability.** The reaction is **monostable** if $(s_k)$ is strictly decreasing and $q_+\ge q_-$ on $[0,1]$, $q_+>0$ on $[0,1]$, $q_+(1)=q_-(1)$, $q_+'(1)<q_-'(1)$ and $(1-\mu)q_+(0)-q_-(0)>0$; it is of **Fisher-KPP type** if moreover $(1-\mu)q_+(U)-q_-(U)\le(1-\mu)q_+(0)-q_-(0)$ on $[0,1]$. Define

$$\alpha_0=1,\qquad \alpha_k=\prod_{i=1}^k\frac{\mu\,s_{i-1}}{(1-\mu)(1-s_i)},$$

the mutation-selection equilibrium ratios $u_k/u_0$, and $\mathfrak Q_{\min}=\min_{[0,1]}q_+$, $\mathfrak Q_{\max}=\max_{[0,1]}q_+$.

**Theorem (proportions are controlled everywhere).** Assume monostability, $\|f\|_{L_\infty(\ell_1)}\le1$, $f_0>0$ on a set of positive measure and $f_k\le\hat\pi_kf_0$ for some $(\hat\pi_k)\in\ell_1^+$. Then there are $\underline\pi(T),\overline\pi(T)\in\ell_1^+$ with $\underline\pi_k(T)\,u_0(T,x)\le u_k(T,x)\le\overline\pi_k(T)\,u_0(T,x)$ for all $k,T,x$ and, in $\ell_1$,

$$\underline\pi(T)\to\big(\alpha_k(\mathfrak Q_{\min}/\mathfrak Q_{\max})^k\big)_k,\qquad \overline\pi(T)\to\big(\alpha_k(\mathfrak Q_{\max}/\mathfrak Q_{\min})^k\big)_k .$$

In particular if $q_+$ is constant (classical Fisher-KPP, $q_+\equiv1$, $q_-(U)=U$), $u_k/u_0\to\alpha_k$ uniformly in space: the front carries the same mutational load as the bulk.

**Theorem (spreading speed).** Under Fisher-KPP type reactions and $\operatorname{supp}f\subset(-\infty,R]$, with

$$c^*=\sqrt{2m\big((1-\mu)q_+(0)-q_-(0)\big)},$$

one has $\sup_{x\ge c^*T}\|u(T,x)\|_{\ell_1}\to0$, and there is $(\nu_k)\in\ell_1^+$ with $\nu_k>0$ such that $\liminf_{T\to\infty}\inf_{x\in[0,(c^*-\varepsilon)T]}u_k(T,x)\ge\nu_k$ for every $k$ and $\varepsilon\in(0,c^*)$.

## Depends on

- [Fisher-KPP travelling waves](../../pattern-formation/fisher-kpp-travelling-waves/README.md)
## Expansion

The ratio bounds come from a Feynman-Kac representation of each $u_k$ along Brownian paths: $u_k$ is fed by $u_{k-1}$ at rate $q_+\mu s_{k-1}$ and decays relative to $u_0$ at rate $q_+(1-\mu)(1-s_k)$, so comparing with the mutation-free class gives ODE-type recursions for $\underline\pi_k,\overline\pi_k$ whose fixed points are $\alpha_k$ distorted by how much the birth rate $q_+$ can vary along a path, hence the factor $(\mathfrak Q_{\max}/\mathfrak Q_{\min})^{\pm k}$. The speed is the linear (pulled) speed of the mutation-free class: at low density the class $k=0$ grows at rate $(1-\mu)q_+(0)-q_-(0)$, and the Fisher-KPP condition makes the linearization an upper bound on the nonlinear growth, giving $c^*=\sqrt{2\cdot\frac m2\cdot2((1-\mu)q_+(0)-q_-(0))}$ in the usual $2\sqrt{Dr}$ form with $D=m/2$. This makes rigorous, under monostability, the Foutel-Rodier-Etheridge prediction obtained by assuming selection-mutation equilibrium at the front.

## Sources

- J. L. de Oliveira Madeira, M. Ortgiese, S. Penington, "Can deleterious mutations surf deterministic population waves?", arXiv:2607.12864 (2026), Section 2 (system of PDEs, Assumptions 1-4, Theorem 2.1, Definition 2.2, Theorems 2.4 and 2.6) and Section 7 (Proposition 7.1, Lemmas 7.2-7.10), <https://doi.org/10.48550/arXiv.2607.12864>.
