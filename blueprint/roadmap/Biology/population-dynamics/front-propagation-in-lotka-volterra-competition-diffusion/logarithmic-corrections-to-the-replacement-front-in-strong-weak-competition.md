# Logarithmic corrections to the replacement front in strong–weak Lotka–Volterra competition

Consider the one-dimensional Lotka–Volterra competition–diffusion system
$$
u_t = u_{xx} + u(1-u-av),\qquad v_t = d\,v_{xx} + r\,v(1-v-bu),\qquad t>0,\ x\in\mathbb{R},
$$
in the **strong–weak** regime $0<a<1<b$, $d>0$, $r>0$: $u$ is the stronger competitor, $(1,0)$ is stable and $(0,1)$ is unstable for the kinetics. Take compactly supported initial data with $0\le u_0,v_0\le 1$, $u_0\not\equiv 0$, $v_0\not\equiv 0$.

Notation:

- $c_u=2$ and $c_v=2\sqrt{rd}$ are the Fisher–KPP speeds of the two species in isolation; assume $c_v>2$ (the weak species is the faster one).
- $c_{\min}=2\sqrt{1-a}$ and $\lambda_{\min}=\sqrt{1-a}$ come from linearizing at $(0,1)$; $c^*\ge c_{\min}$ is the minimal speed of monotone fronts connecting $(1,0)$ to $(0,1)$.
- $b^*=b^*(a,d,r)$ is the pulled-to-pushed threshold: $c^*=c_{\min}$ for $0<b\le b^*$ and $c^*>c_{\min}$ for $b>b^*$.
- $f(c)=c-\sqrt{c^2-4(1-a)}+2\sqrt a$ for $c\ge c_{\min}$. The **nonlocal pulling speed** $c^{**}$ solves $f(c^{**})=c_v$, i.e. $c^{**}=\sqrt{rd}-\sqrt a+\dfrac{1-a}{\sqrt{rd}-\sqrt a}$, with decay rate $\lambda^{**}=\tfrac{c^{**}}{2}-\sqrt{\tfrac{(c^{**})^2}{4}-(1-a)}$.
- $\eta_v=3d/c_v$ is the coefficient of the Bramson-type logarithmic lag of the fast $v$-front.

For $\theta\in(0,1)$ let $X_\theta(t)=\sup\{x: u(t,x)\ge\theta\}$ be the rightmost $\theta$-level of the strong species, which marks the replacement front where $u$ invades the territory already taken by $v$.

**Theorem.** Exactly one of the following holds.

1. **Strict nonlocal pulling**, $2<c_v<f(c^*)$:
$$X_\theta(t)=c^{**}t-\frac{\tfrac32-\sqrt a\,\eta_v}{\lambda^{**}}\log t+O_\theta(1).$$
2. **Pushed**, $c^*>c_{\min}$ and $c_v\ge f(c^*)$: $X_\theta(t)=c^*t+O_\theta(1)$, with no logarithmic correction.
3. **Critical nonlocal line, pulled tail**, $c^*=c_{\min}$, $c_v=f(c_{\min})$, $1<b<b^*$:
$$X_\theta(t)=c_{\min}t-\frac{\tfrac54-\tfrac12\sqrt a\,\eta_v}{\lambda_{\min}}\log t+O_\theta(1).$$
4. **Critical nonlocal line at the transition**, $c^*=c_{\min}$, $c_v=f(c_{\min})$, $b=b^*$:
$$X_\theta(t)=\begin{cases}c_{\min}t-\dfrac{1}{2\lambda_{\min}}\log t+O_\theta(1), & \sqrt a\,\eta_v<\tfrac12,\\[2mm] c_{\min}t-\dfrac{1}{2\lambda_{\min}}\log t+\dfrac{1}{\lambda_{\min}}\log\log t+O_\theta(1), & \sqrt a\,\eta_v=\tfrac12,\\[2mm] c_{\min}t+\dfrac{-\tfrac32+\sqrt a\,\eta_v}{2\lambda_{\min}}\log t+O_\theta(1), & \sqrt a\,\eta_v>\tfrac12.\end{cases}$$
The resonance $\sqrt a\,\eta_v=\tfrac12$ is equivalent to $3d\sqrt a=\sqrt a+\sqrt{1-a}$.
5. **Local pulling**, $c^*=c_{\min}$ and $c_v>f(c_{\min})$: $X_\theta(t)=c_{\min}t-\dfrac{3}{2\lambda_{\min}}\log t+O_\theta(1)$ if $1<b<b^*$, and $X_\theta(t)=c_{\min}t-\dfrac{1}{2\lambda_{\min}}\log t+O_\theta(1)$ if $b=b^*>1$.

## Depends on

- [Fisher–KPP fronts exist exactly at or above the minimal speed](../../pattern-formation/fisher-kpp-travelling-waves/exists-is-front-iff.md)

## Expansion

The first-order speed $\max\{c^{**},c^*\}$ (with $c^{**}$ only relevant when $c_v<f(c_{\min})$) comes from earlier work on propagating terraces: $v$ invades empty space at speed $c_v$, and $u$ then replaces $v$ either at its own minimal speed $c^*$ or, when the $v$-front is not far enough ahead, at the faster speed $c^{**}$ set by the exponential tail that the $v$-front leaves behind. The theorem refines this to the logarithmic order. The proof changes variables to make the system cooperative and builds piecewise sub- and supersolutions. The fast front carries the Bramson lag $\eta_v\log t$. Heat-kernel estimates for a moving potential and a ground-state transform turn that lag into a logarithmic phase drift of the slow front. The drift reduces the classical $\tfrac32$ coefficient by $\sqrt a\,\eta_v$ (nonlocal pulling), changes it to $\tfrac54$ on the critical line (pulled tail $(A\xi+B)e^{-\lambda_{\min}\xi}$ with $A>0$), and produces the three-way split at $b=b^*$, where $A=0$ and the transition front has a pure exponential tail. Pushed fronts are locked to $c^*t$ with bounded error.

## Sources

- H. Guo, D. Xiao, M. Zhou, "Sharp logarithmic corrections for a strong-weak Lotka-Volterra competition system", arXiv preprint (2026), Theorem 1.1 and Section 1 (setup and notation), <https://doi.org/10.48550/arXiv.2608.11956>.
