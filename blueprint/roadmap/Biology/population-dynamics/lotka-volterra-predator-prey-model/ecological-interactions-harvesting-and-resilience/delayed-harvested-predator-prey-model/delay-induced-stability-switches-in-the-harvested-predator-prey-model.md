# Delay-induced stability switches in the harvested predator–prey model

**Model.** Prey $x$ with delayed logistic self-limitation and predator $y$, both harvested at constant rates:

$$
\dot x(t)=rx(t)-ax(t)x(t-\tau)-bx(t)y(t)-h,\qquad \dot y(t)=cx(t)y(t)-dy(t)-k,
$$

with all parameters positive ($a=r/K$) and delay $\tau\ge0$. Positive equilibria $E^*=(x^*,y^*)$ solve $y=(rx-ax^2-h)/(bx)=k/(cx-d)$ and require $r^2>4ah$ and $cx^*>d$.

**Characteristic equation.** Linearizing at $E^*$ gives $\dot X=AX(t)+BX(t-\tau)$ with $A=\begin{pmatrix}r-ax^*-by^*&-bx^*\\cy^*&cx^*-d\end{pmatrix}$, $B=\begin{pmatrix}-ax^*&0\\0&0\end{pmatrix}$, hence

$$
\lambda^2+a_1\lambda+a_2+(a_3\lambda+a_4)e^{-\lambda\tau}=0,
$$

$$
a_1=-(r-ax^*-by^*)-(cx^*-d),\quad a_2=(r-ax^*-by^*)(cx^*-d)+bcx^*y^*,\quad a_3=ax^*,\quad a_4=-ax^*(cx^*-d).
$$

**Theorem.**

1. *(No delay.)* For $\tau=0$, $E^*$ is locally asymptotically stable iff $a_1+a_3>0$ and $a_2+a_4>0$.
2. *(Crossing frequencies.)* Assume the $\tau=0$ conditions. Then $\lambda=0$ is never a root, and $\lambda=\pm i\omega$ ($\omega>0$) is a root for some $\tau$ iff $u=\omega^2$ is a positive root of

$$
h(u)=u^2+\alpha u+\beta,\qquad \alpha=a_1^2-2a_2-a_3^2,\quad \beta=a_2^2-a_4^2 .
$$

   The number of positive roots of $h$ is $0$ if $\alpha\ge0,\beta\ge0$; $1$ if $\beta<0$ (any $\alpha$), or if $\alpha<0,\beta=0$; and, if $\alpha<0<\beta$, it is $0$, $1$ or $2$ according as the vertex value $h(-\alpha/2)$ is $>0$, $=0$ or $<0$. In particular, if $h$ has no positive root (e.g. $\alpha>0,\beta>0$), $E^*$ is stable for all $\tau\ge0$ (absolute stability).
3. *(Critical delays.)* If $h$ has positive roots $u_\pm=\omega_\pm^2$, purely imaginary roots $\pm i\omega_\pm$ occur exactly at

$$
\tau_k^\pm=\frac1{\omega_\pm}\Big[\arctan\frac{\omega_\pm(a_3\omega_\pm^2+a_1a_4-a_2a_3)}{(a_4-a_1a_3)\omega_\pm^2-a_2a_4}+2\pi k\Big],\qquad k=0,1,2,\dots
$$

   (branch of $\arctan$ chosen consistently with $\sin\omega\tau$ and $\cos\omega\tau$ from the real and imaginary parts).
4. *(Transversality.)* $\operatorname{sign}\,\frac{d\,\mathrm{Re}\,\lambda}{d\tau}\big|_{\tau=\tau_k^\pm}=\operatorname{sign}h'(u_\pm)$. With two positive roots $u_-<u_+$, crossings at $\tau_k^+$ go to the right half-plane and crossings at $\tau_k^-$ go back (the source's Section 2.4).

## Expansion

Substituting $\lambda=i\omega$ and separating real and imaginary parts gives $a_4\cos\omega\tau+a_3\omega\sin\omega\tau=\omega^2-a_2$ and $a_4\sin\omega\tau-a_3\omega\cos\omega\tau=a_1\omega$. Squaring and adding eliminates $\tau$ and yields the quartic $\omega^4+\alpha\omega^2+\beta=0$, i.e. $h(\omega^2)=0$; solving the two linear equations for $\sin$ and $\cos$ gives the critical delays. Because the spacing $2\pi/\omega_+$ of destabilizing crossings is shorter than the spacing $2\pi/\omega_-$ of stabilizing ones, the $\tau_k^+$ sequence eventually overtakes the $\tau_k^-$ sequence, which is the mechanism behind stability switches on a bounded delay interval; the source does not prove a general switching theorem, but in its example (Section 3) $E^*$ changes stability five times. For the parameter values $r=3.5$, $a=0.04$, $b=1$, $c=0.05$, $d=0.3$, $h=0.02$, $k=0.01$, the interior equilibrium $E_1\approx(6.061,3.254)$ has $\alpha<0<\beta$, $h(\bar u)<0$, $\omega_-\approx0.879$, $\omega_+\approx1.122$, and first destabilizing delay $\tau_0^+\approx1.379$; numerical continuation confirms the Hopf points and the emerging periodic orbits.

## Proof depends on

- [Routh–Hurwitz: a real 2 × 2 matrix is Hurwitz iff tr M < 0 < det M](../../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-hurwitz-iff-trace-neg-and-det-pos.md)
- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)

## Sources

- Juancho A. Collera, "Numerical Continuation and Bifurcation Analysis in a Harvested Predator-Prey Model with Time Delay using DDE-Biftool", arXiv:2009.12666 (2020), Section 2 (model, local stability, Lemma 1, critical delays, transversality) and Section 3 (numerical continuation), <https://doi.org/10.48550/arXiv.2009.12666>.
