# Integral representation of the linear-determinacy threshold

Consider the Lotka–Volterra competition–diffusion system
$$
u_t=u_{xx}+u(1-u-av),\qquad v_t=d\,v_{xx}+r\,v(1-v-bu),\qquad x\in\mathbb{R},
$$
in the **monostable** regime $0<a<1$, $b>0$, $d,r>0$, where $u$ invades the state $(0,1)$. Linearizing at $(0,1)$ gives the candidate speed $c_0=2\sqrt{1-a}$, and the minimal front speed satisfies $c^*(a,b,d,r)\ge c_0$. *Linear determinacy* means $c^*=c_0$ (pulled front); *nonlinear determinacy* means $c^*>c_0$ (pushed front). There is a unique threshold $b_0(a,d,r)\in(0,\infty)$ with
$$
c^*=c_0\ \text{ for } 0<b\le b_0,\qquad c^*>c_0\ \text{ for } b>b_0 .
$$
Unlike the standing-front problem, this speed does not depend on $d,r$ only through $d/r$.

**Gaussian recursion.** Let $A(\beta)=\dfrac{1-a}{1-a\min\{\beta,1\}}$. Let $f_a(x)=\tfrac{1-a}{2}\cos^2(\pi x/2)$ for $|x|\le1$ and $f_a(x)=0$ otherwise, and let $G_{\kappa,h}$ be the heat kernel of variance $2\kappa h$. For $m\ge1$ set $K_\beta=2+r(1+\beta)$, $N=\lceil K_\beta m^2e^{m^2}\rceil$, $h=m/N$. Start from $p_0=f_a$, $q_0=0$ and iterate, for $0\le k<N$,
$$
p_{k+1}=G_{1,h}*\bigl[p_k+h\,p_k(1-a-p_k+aq_k)\bigr],\qquad
q_{k+1}=G_{d,h}*\bigl[q_k+hr(1-q_k)(\beta p_k-q_k)\bigr].
$$
Define the total mass and the speed gap
$$
M_m(\beta)=\int_{\mathbb{R}}p_N(x)\,dx,\qquad D_m(\beta)=\Bigl(\frac{M_m(\beta)}{2A(\beta)m}-2\sqrt{1-a}\Bigr)_+ .
$$

**Theorem.** For every $0<a<1$ and $d,r>0$:

1. $c^*(a,b,d,r)=\lim_{m\to\infty}\dfrac{M_m(b)}{2A(b)\,m}$ for every $b>0$.
2. Linear determinacy holds iff $\lim_{m\to\infty}D_m(b)=0$; nonlinear determinacy holds iff $\lim_{m\to\infty}D_m(b)>0$.
3. $$b_0(a,d,r)=-\log\Bigl[\lim_{n\to\infty}\lim_{m\to\infty}\int_0^\infty e^{-\beta}\bigl(1-e^{-nD_m(\beta)}\bigr)\,d\beta\Bigr],$$ where the inner limit is taken with $n$ fixed and the bracket equals $e^{-b_0}\in(0,1)$.

## Expansion

From compactly supported data, $u$ spreads in both directions at the minimal speed $c^*$ toward the equilibrium $(A(\beta),\cdot)$ reached behind the front ($(1-a)/(1-a\beta)$ for weak competition, $1$ for $\beta\ge1$). So the total mass grows like $2A(\beta)c^*t$, and the normalized mass recovers $c^*$. A splitting error estimate with $T=m$ shows that the Gaussian recursion tracks the exact evolution. The gap $D_m$ then tends to $0$ on $(0,b_0]$ and to a positive limit on $(b_0,\infty)$, so $1-e^{-nD_m}$ tends to the indicator of $(b_0,\infty)$ as $m\to\infty$ and then $n\to\infty$. Integrating against $e^{-\beta}$ gives $e^{-b_0}$. Existence and uniqueness of $b_0$ come from an earlier classification of minimal waves; the result here is an explicit integral–limit formula that needs no wave profile.

## Sources

- S. Ma, D. Xiao, M. Zhou, "Sharp Thresholds for Linear Determinacy and Zero Wave Speed in Lotka-Volterra Competition-Diffusion Systems", arXiv preprint (2026), Theorem 1.2 and Sections 6–9, <https://doi.org/10.48550/arXiv.2610.16748>.
