# Stability and Hopf bifurcation of a stem-cell model with distributed cell-cycle duration

**Model.** Hematopoietic stem cells are either resting ($G_0$ phase, total population $x(t)$) or proliferating ($y(t)$). Resting cells die at rate $\delta\ge0$ and enter the cycle at a density-dependent rate $\beta(x)$, where $\beta$ is positive, decreasing and tends to $0$ at infinity; a Hill function $\beta(x)=\beta_0\theta^n/(\theta^n+x^n)$ is typical. Proliferating cells undergo apoptosis at rate $\gamma\ge0$. The cell-cycle duration $\tau$ is random with density $f$ supported on $[\underline\tau,\overline\tau]$, $0\le\underline\tau<\overline\tau$. At the end of the cycle each cell divides into two resting cells. Integrating the two age-structured transport equations over age gives, for $t\ge\overline\tau$,

$$\frac{dx}{dt}=-\big(\delta+\beta(x(t))\big)x(t)+2\int_{\underline\tau}^{\overline\tau}e^{-\gamma\tau}f(\tau)\,\beta(x(t-\tau))\,x(t-\tau)\,d\tau,$$

$$\frac{dy}{dt}=-\gamma y(t)+\beta(x(t))x(t)-\int_{\underline\tau}^{\overline\tau}e^{-\gamma\tau}f(\tau)\,\beta(x(t-\tau))\,x(t-\tau)\,d\tau .$$

The $x$-equation is closed. Here $y$ is determined by the history of $x$, and $y$ converges, or is periodic, whenever $x$ is. Write $K=\int_{\underline\tau}^{\overline\tau}e^{-\gamma\tau}f(\tau)\,d\tau$ for the probability of surviving one cycle.

**Theorem.**

1. *(Boundedness.)* If $\delta>0$, all solutions are bounded. If $\delta=0$, $K>\frac12$, $x\beta(x)$ is eventually decreasing and the initial value is large enough, then $x(t)\to+\infty$.
2. *(Trivial equilibrium.)* The equilibrium $(0,0)$ is globally asymptotically stable if $(2K-1)\beta(0)<\delta$, and unstable if $\delta<(2K-1)\beta(0)$.
3. *(Positive equilibrium.)* A unique positive equilibrium $E^*=(x^*,y^*)$ exists if and only if $0<\delta<(2K-1)\beta(0)$; then $\beta(x^*)=\delta/(2K-1)$. Let $\beta^*=\frac{d}{dx}\big(x\beta(x)\big)\big|_{x^*}$ and $\widetilde\delta=-\delta/(2K+1)$. If $\beta^*\ge\widetilde\delta$, then $E^*$ is locally asymptotically stable for all delay distributions.
4. *(Hopf bifurcation.)* Suppose $\tau\mapsto e^{-\gamma\tau}f(\tau)$ is decreasing. Then for every $\delta$ satisfying the existence condition, except a finite exceptional set, there is $\beta^*_c<\widetilde\delta$ with the following property. $E^*$ is locally asymptotically stable for $\beta^*_c<\beta^*\le\widetilde\delta$, and a Hopf bifurcation occurs at $\beta^*=\beta^*_c$. There the characteristic equation

$$\lambda+\delta+\beta^*-2\beta^*\int_{\underline\tau}^{\overline\tau}e^{-(\lambda+\gamma)\tau}f(\tau)\,d\tau=0$$

has a pair of simple roots $\pm i\omega_c$ crossing transversally, so periodic solutions branch off.

The oscillations are proposed as a mechanism for periodic chronic myelogenous leukemia, in which blood counts oscillate with periods longer than the cell cycle.

## Expansion

Global stability of $0$ uses a Lyapunov functional on the history segment $\varphi=x_t$:

$$J(\varphi)=B(\varphi(\overline\tau))+\int_{\underline\tau}^{\overline\tau}e^{-\gamma\tau}f(\tau)\int_{\overline\tau-\tau}^{\overline\tau}\big(\beta(\varphi(\theta))\varphi(\theta)\big)^2\,d\theta\,d\tau,\qquad B(x)=\int_0^x\beta(s)s\,ds .$$

Its upper right derivative is bounded with the inequality $2ab\le a^2+b^2$ and is nonpositive under the stated condition. The LaSalle invariance principle then concludes. For $E^*$, the linearization $\dot u=-(\delta+\beta^*)u+2\beta^*\int e^{-\gamma\tau}f(\tau)u(t-\tau)\,d\tau$ gives the characteristic equation above. Purely imaginary roots $i\omega$ must satisfy $\delta=g(\omega):=\omega(1-2C(\omega))/(2S(\omega))$, where $C$ and $S$ are the cosine and sine transforms of $e^{-\gamma\tau}f(\tau)$. When $e^{-\gamma\tau}f$ is decreasing, an induction over the half-periods $\omega\overline\tau\in(k\pi,(k+1)\pi]$ shows $S(\omega)>0$ for all $\omega>0$. This yields a solution $(\beta^*_c,\omega_c)$ and the transversality sign $-C'(\omega_c)-\delta(S/\omega)'(\omega_c)\neq0$ off the finite set of critical values of $g$. Destabilization therefore needs $\beta^*$ sufficiently negative, that is, a steep decrease of the cycle-entry rate near $x^*$.

The statements are Lemma 2.1 and Propositions 2.1–2.2 (Section 2), Theorems 3.1–3.2 on the trivial and nontrivial equilibria (Section 3), and the Hopf Lemma 4.1 and Theorem 4.1 (Section 4) of the source.

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Sources

- M. Adimy, F. Crauste, S. Ruan, "A mathematical study of the hematopoiesis process with applications to chronic myelogenous leukemia", arXiv:0904.2493 (2009) <https://doi.org/10.48550/arXiv.0904.2493>
