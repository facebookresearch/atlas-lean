# Delay stability window and paired Hopf bifurcations in the Burns–Tannock equation

Consider the stem cell equation $Q'(t)=-(\kappa+\beta(Q(t)))Q(t)+A\beta(Q(t-\tau))Q(t-\tau)$ with Hill rate $\beta(Q)=f\theta^s/(\theta^s+Q^s)$ and amplification $A=2e^{-\gamma\tau}$, in the regime $\kappa<f(A-1)$ where the positive steady state $Q^*$ exists. Put $h(x)=x\beta(x)$ and linearize, $z'(t)=az(t)+bz(t-\tau)$, with

$$a=-\kappa-h'(Q^*),\qquad b=A\,h'(Q^*),$$

so that the characteristic equation is the Hayes equation $\lambda-a-be^{-\lambda\tau}=0$.

**Theorem.** (i) $a+b=(A-1)Q^*\beta'(Q^*)$ satisfies $-s\kappa<a+b<0$, so $Q^*$ can lose stability only through a pair of purely imaginary roots, that is, by crossing the curve $C_0=\{(\omega\cot\omega/\tau,\,-\omega\csc\omega/\tau):\omega\in[0,\pi)\}$. (ii) In the region $b\le-|a|$, $Q^*$ is asymptotically stable for $\tau<\tau_1(a,b)=\arccos(-a/b)/\sqrt{b^2-a^2}$ and unstable for $\tau>\tau_1$; for $a<-|b|$ it is stable for every delay. (iii) $Q^*$ is stable for all sufficiently small $\tau$ (at $\tau=0$ the root is $a+b<0$) and for all $\tau$ above

$$\tau_2=\frac1\gamma\ln\Big(\frac12\Big[1+\frac{\kappa s}{f(s-1)}\Big]\Big)^{-1},$$

where $b>0$ places $(a,b)$ in the delay-independent region. Therefore Hopf bifurcations of $Q^*$ under variation of $\tau$ occur in pairs $\tau_1^-<\tau_1^+$, solutions of the implicit equation $\tau=\tau_1(a(\tau),b(\tau))$, giving a bounded instability window $(\tau_1^-,\tau_1^+)$. The value $\tau_2$, where $b=0$, lies inside the stability region and is not a stability boundary. The higher Hopf curves $C_{2n}$ ($\omega\in[2n\pi,(2n+1)\pi)$) never intersect, so there are no double-Hopf points.

At the homeostatic parameters ($\gamma=0.1$, $f=8$, $s=2$, $\tau=2.8$ days, $Q^h=1.1$) the steady state is stable, and varying $\tau$ alone gives $\tau_1^-\approx5.749<\tau_1^+\approx6.874<\tau_2\approx6.877<\tau_{\max}\approx6.904$ days.

## Expansion

The stability chart of $z'=az+bz(t-\tau)$ is classical: roots cross the imaginary axis only on the curves $C_{2n}$, and the first crossing is on $C_0$. Unlike delay equations whose steady state gains ever more unstable roots as the delay grows (such as Mackey–Glass), here the mortality factor $A=2e^{-\gamma\tau}$ makes $b$ change sign at $\tau_2$, so increasing the cell cycle duration eventually restabilizes the steady state. Periodic orbits born at $\tau_1^\pm$ have period $2\pi/\omega$; numerically they undergo folds, period doubling, torus bifurcations and a canard explosion with periods from weeks to years, relevant to periodic hematological diseases.

## Depends on

- [Well-posedness and steady states of the Burns–Tannock stem cell equation](well-posedness-and-steady-states-of-the-burns-tannock-stem-cell-equation.md)

## Sources

- D. C. De Souza and A. R. Humphries, *Dynamics of a mathematical hematopoietic stem-cell population model*, arXiv:1712.08308 (2017), Section 2.1 (Stability Boundary) and Sections 3–5. <https://doi.org/10.48550/arXiv.1712.08308>
