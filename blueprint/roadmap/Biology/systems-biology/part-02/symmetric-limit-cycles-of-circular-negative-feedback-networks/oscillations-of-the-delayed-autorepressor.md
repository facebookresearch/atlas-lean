# Oscillations of the delayed autorepressor

**Model (Eq. 1).** A gene represses its own synthesis after a delay $\tau\ge0$:

$$\frac{dx}{dt}=\frac{\alpha}{1+x(t-\tau)^h}-x(t),\qquad \alpha>0,\ h>0.$$

It has a unique positive equilibrium $x_0$, defined by $x_0(1+x_0^h)=\alpha$.

**Loss of stability.** Let $w=hx_0^h/(1+x_0^h)$. For $\tau=0$ the equilibrium is globally attracting. If $w>1$, put $u=\sqrt{w^2-1}$; then the equilibrium loses stability at

$$\tau^*=\frac{\pi-\arctan u}{u},$$

where a limit cycle appears with period $2\pi/u$.

**Step-function limit (Eqs. 4–7).** As $h\to\infty$ the feedback becomes a switch: $\dot x=\alpha-x$ when $x(t-\tau)<1$ and $\dot x=-x$ when $x(t-\tau)>1$. For $\alpha>1$ and $\tau>0$ this equation has a limit cycle with period

$$T(\tau)=\ln\frac{(\alpha e^{\tau}-\alpha+1)(\alpha e^{\tau}-1)}{\alpha-1},$$

and $T(\tau) > 2\tau$ for every $\tau > 0$. For every $\tau > 0$ the equation also has a countable family of further cycles $C_k$, $k \ge 1$ (Lemma 1): $s \mapsto s + kT(s)$ increases continuously from $0$, so there is a unique $\tau_k \in (0,\tau)$ with $\tau_k + kT(\tau_k) = \tau$, and the $T(\tau_k)$-periodic cycle of the equation with delay $\tau_k$ also solves it with delay $\tau$, since its delayed values repeat after $kT(\tau_k)$. These have periods $T(\tau_k) < \tau/k < 2\tau$, so the cycle of period $T(\tau)$ is the only one with period above $2\tau$. (The source states the family under the condition $T(\tau) < 2\tau$, which never holds.)

## Expansion

Linearizing at $x_0$ and using $\alpha=x_0(1+x_0^h)$ gives the feedback slope $-w$, so the characteristic equation is $\lambda+1=-we^{-\lambda\tau}$. A root $\lambda=iu$ requires $|1+iu|=w$, i.e. $u^2=w^2-1$, together with $\cos(u\tau)=-1/w$ and $\sin(u\tau)=u/w$, which give $u\tau=\pi-\arctan u$. In the switch limit the solution is piecewise exponential, relaxing toward $\alpha$ or toward $0$. The switching times are the times at which the solution crossed the threshold $1$ one delay earlier, and matching the pieces over one period gives $T(\tau)$ in closed form. Numerically, for $\tau>\tau^*$ the finite-$h$ equation shows one stable cycle, of period above $2\tau$.

## Sources

- V. A. Likhoshvai, V. P. Golubyatnikov, T. M. Khlebodarova, "Limit cycles in models of circular gene networks regulated by negative feedback loops", BMC Bioinformatics (2020). <https://doi.org/10.1186/s12859-020-03598-z>, PMCID PMC7488683. Section on the one-element network, Eqs. (1) and (4)–(8), Lemma 1.
