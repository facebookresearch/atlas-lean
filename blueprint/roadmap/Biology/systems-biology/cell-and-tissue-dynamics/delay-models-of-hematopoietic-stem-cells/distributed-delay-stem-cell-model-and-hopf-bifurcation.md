# Distributed-delay stem cell model and Hopf bifurcation

**Model.** The resting pluripotent stem cell density $x(t)$ satisfies

$$x'(t)=-\bigl(\delta+\beta(x(t))\bigr)x(t)+\frac{2}{\tau-\tau_{\min}}\int_{\tau_{\min}}^{\tau}\beta(x(t-r))\,x(t-r)\,dr,$$

where $\delta>0$ is the loss rate by death and differentiation, cells re-enter the cell cycle at the Hill rate $\beta(x)=\beta_0\theta^n/(\theta^n+x^n)$, and the cell-cycle duration is uniformly distributed on $[\tau_{\min},\tau]$; each dividing cell returns two daughters.

**Theorems.**
1. A positive equilibrium exists iff $\beta_0>\delta>0$, and then $x^*=\theta(\beta_0/\delta-1)^{1/n}$.
2. If $\beta_0<\delta$, the trivial equilibrium is globally stable.
3. Take $\tau_{\min}=0$. If $n(\beta_0-\delta)/\beta_0\le1$, then $x^*$ is locally asymptotically stable for every $\tau$; it remains so for every $\tau$ when $1<n(\beta_0-\delta)/\beta_0<\frac{2(1-u_0)}{1-2u_0}$, where $u_0=\min_{x\ge0}\frac{\sin x}{x}\in(-1,0)$.
4. *(Hopf bifurcation.)* Let $h(x)=\frac{2(1-x)}{1-2x}$ for $x\in[-1,\tfrac12)$, with $h(1)=+\infty$. Under the complementary condition $h(u_0)\le n(\beta_0-\delta)/\beta_0$ and $\delta+\beta^*\ne0$, where $\beta^*=\frac{d}{dx}(\beta(x)x)|_{x^*}$, the characteristic equation has finitely many crossing pairs $(\tau_c,\omega_c)$, and a Hopf bifurcation occurs at the smallest crossing $\tau_0$: $x^*$ is locally asymptotically stable for $0\le\tau<\tau_0$ and unstable on $[\tau_0,\tau_l]$, with $\tau_l$ the largest destabilizing crossing.
5. For $\delta=0.05\,\mathrm{d}^{-1}$, $\beta_0=1.77\,\mathrm{d}^{-1}$ and $n=3$ there is a unique bifurcation value $\tau_c\approx18$ days, beyond which $x^*$ is unstable; the bifurcating periodic solution has period close to $46$ days, the time scale of periodic hematological diseases.

## Expansion

Linearizing at $x^*$ with $\tau_{\min}=0$ gives a characteristic equation of the form $\lambda+\delta+\beta^*=2\beta^*\frac{1-e^{-\lambda\tau}}{\lambda\tau}$; purely imaginary roots $\lambda=i\omega$ lead to the equations $\sin$ and $\cos$ of $\omega\tau$ whose solvability is controlled by the extrema of $\sin x/x$, which is where $u_0$ and the points $x_k$ enter. Delay-independent stability holds when the right-hand side cannot balance the left for real frequencies. At each crossing the sign of $d\operatorname{Re}\lambda/d\tau$ is determined by which interval $(x_k,x_{k+1})$ contains $\omega_c\tau_c$, giving destabilizing and restabilizing crossings and the Hopf bifurcation at the first destabilizing one.

## Sources

- M. Adimy, F. Crauste, S. Ruan, "Stability and Hopf bifurcation in a mathematical model of pluripotent stem cell dynamics", arXiv:0904.2491 (2009), Section 2 (model, Proposition 2.1, parameter values), Theorems 3.1–3.3, Lemma 4.1, Propositions 4.1–4.2, Theorem 4.1 and Corollary 4.1, <https://doi.org/10.48550/arXiv.0904.2491>.
