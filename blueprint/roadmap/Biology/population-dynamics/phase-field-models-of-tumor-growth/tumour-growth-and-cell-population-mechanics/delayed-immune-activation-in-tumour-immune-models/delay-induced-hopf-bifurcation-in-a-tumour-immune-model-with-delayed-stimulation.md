# Delay-induced Hopf bifurcation in a tumour–immune model with delayed stimulation

**Model.** Let $x(t)$ be the non-dimensional level of immune effector cells and $y(t)$ the tumour size. Effector cells have background (native) supply $\omega>0$, turnover rate normalized to $1$ on the time scale $d>0$, stimulation strength $\rho>0$, and anti-immune (tumour-mediated inactivation) strength $\psi\ge0$. The stimulation responds to the tumour size a time $\tau\ge0$ earlier, the time needed to mount an immune response:

$$\frac{dx}{dt}=d\big(\omega-x(t)+\rho f(y(t-\tau))\,x(t)-\psi\,x(t)y(t)\big),\qquad \frac{dy}{dt}=y(t)\big(1-x(t)\big).$$

The stimulus $f$ is increasing, saturating and smooth with $f(0)=0$; the main example is the Hill function $f(y)=y^\alpha/(1+y^\alpha)$ with $\alpha\ge1$. Initial data are nonnegative continuous functions on $[-\tau,0]$.

**Theorem.**

1. For nonnegative continuous initial data there is a unique global solution, and it stays nonnegative.
2. The tumour-free steady state $A=(\omega,0)$ is a locally stable node if $\omega>1$ and a saddle if $\omega<1$, for every $\tau\ge0$.
3. Every positive steady state has the form $(1,\zeta)$, where $\zeta>0$ solves $\omega-1+\rho f(\zeta)-\psi\zeta=0$. For $\psi=0$ and the Hill stimulus there is no positive steady state if $\omega>1$. If $\max\{0,1-\rho\}<\omega<1$ there is exactly one, with $\zeta=\big(\frac{1-\omega}{\rho+\omega-1}\big)^{1/\alpha}$.
4. Let $\gamma_f=\rho f'(\zeta)>0$ at a positive steady state.
 - If $\psi>\gamma_f$, then $(1,\zeta)$ is unstable for all $\tau\ge0$.
 - If $\psi<\gamma_f$, then $(1,\zeta)$ is locally asymptotically stable for $\tau=0$. It stays stable for $\tau<\tau_{cr}$ and becomes unstable for $\tau>\tau_{cr}$, and at $\tau=\tau_{cr}$ a Hopf bifurcation produces periodic solutions with period $2\pi/\sqrt{\eta}$. Here

$$\eta=\frac{-\big(2d\zeta\psi+(d\omega)^2\big)+\sqrt{(d\omega)^4+4d^3\zeta\psi\omega^2+4(d\zeta\gamma_f)^2}}{2},\qquad \tau_{cr}=\frac{1}{\sqrt\eta}\arccos\Big(\frac{\eta+d\zeta\psi}{d\zeta\gamma_f}\Big).$$

So when the immune system responds to the tumour faster than it is inactivated by it ($\gamma_f>\psi$), a dormant tumour equilibrium exists. This equilibrium is lost to sustained oscillations once the activation delay exceeds $\tau_{cr}$. This offers a mechanism for oscillating tumour burdens.

## Expansion

At $(1,\zeta)$, the steady-state relation $\omega=1-\rho f(\zeta)+\psi\zeta$ simplifies the linearization. The characteristic equation is

$$W(\lambda)=\lambda^2+d\,\omega\lambda-d\zeta\psi+d\zeta\gamma_fe^{-\lambda\tau}=0 .$$

At $\tau=0$ the constant term is $d\zeta(\gamma_f-\psi)$, so $\psi>\gamma_f$ gives a positive real root, and such a root persists for every delay. For $\psi<\gamma_f$, substituting $\lambda=i\sqrt\eta$ and separating real and imaginary parts gives

$$(d\zeta\gamma_f)^2=(\eta+d\zeta\psi)^2+(d\omega)^2\eta .$$

This quadratic in $\eta$ has the unique positive root above. The real part gives $\cos(\sqrt\eta\,\tau)=(\eta+d\zeta\psi)/(d\zeta\gamma_f)$, and hence $\tau_{cr}$. The semi-trivial state has characteristic roots $-d$ and $1-\omega$, since $f(0)=0$ makes the delayed term drop out, which explains its delay independence. The non-scaled model is fitted to BCL$_1$ lymphoma growth data in normal and chimeric mice.

The statements are the base-model propositions (Section 2) and the existence and stability theorems (Section 3) of the source.

## Proof depends on

- [Routh–Hurwitz: a real 2 × 2 matrix is Hurwitz iff tr M < 0 < det M](../../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-hurwitz-iff-trace-neg-and-det-pos.md)
- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)

## Sources

- M. J. Piotrowska, "An immune system–tumour interactions model with discrete time delay: model analysis and validation", arXiv:1505.02030 (2015). <https://doi.org/10.48550/arXiv.1505.02030>
