# Delay-induced Hopf bifurcation in a sterile insect model with residually fertile releases

**Model.** Let $w$, $g$ and $s$ be the densities of wild, sterile and non-sterile (residually fertile, released) mosquitoes, $N=w+g+s$. Sterile insects are released at the saturated rate $bw/(1+w)$, a fraction of releases is fertile and enters $s$ at rate $cw/(1+w)$ (residual fertility $c$), wild and non-sterile insects reproduce with per-mating offspring rates $a$ and $r$, and all classes suffer density-dependent mortality $\xi_iN$. With a maturation delay $\tau>0$ in the cross-reproduction terms:

$$\dot w=\Bigl(\frac{aw+rs(t-\tau)}{1+w+g+s(t-\tau)}-\xi_1\bigl(w+g+s(t-\tau)\bigr)\Bigr)w,\qquad \dot g=\frac{bw}{1+w}-\xi_2(w+g+s)\,g,$$

$$\dot s=\frac{cw}{1+w}+\Bigl(\frac{rs+aw(t-\tau)}{1+w(t-\tau)+g+s}-\xi_3\bigl(w(t-\tau)+g+s\bigr)\Bigr)s.$$

The delay does not change the equilibria. Besides the origin, there is the boundary equilibrium $E^0=(0,0,s^0)$ with $s^0=(r-\xi_3)/\xi_3$ when $r>\xi_3$ (only the fertile released strain persists), and positive equilibria $E^\ast=(w^\ast,g^\ast,s^\ast)$ determined by the total equilibrium population.

**Theorem.** Linearize at a positive equilibrium $E^\ast$; the characteristic equation is a cubic quasi-polynomial in $\lambda$ with terms $e^{-\lambda\tau}$ and $e^{-2\lambda\tau}$. Separating $\lambda=i\omega$ gives an auxiliary polynomial equation in $\omega$ with a distinguished coefficient $\gamma_6$: if $\gamma_6>0$ (and the delay-free system is stable) all roots have negative real parts for every delay and $E^\ast$ is locally asymptotically stable; if $\gamma_6<0$ the auxiliary equation has a positive root. In that case, under the stated nondegeneracy hypotheses, there are purely imaginary roots $\pm i\omega_k$ at a sequence of critical delays $\tau_k^{(j)}$ ($k=1,\dots,6$, $j=0,1,2,\dots$), the crossing is transversal,

$$\operatorname{sign}\,\operatorname{Re}\Bigl(\frac{d\lambda}{d\tau}\Bigr)^{-1}\Big|_{\tau=\tau_k^{(j)}}>0,$$

and consequently:

1. $E^\ast$ is asymptotically stable for $\tau\in[0,\tau_0)$, where $\tau_0=\min_k\tau_k^{(0)}$ is the first critical delay;
2. at each $\tau=\tau_k^{(j)}$ the system undergoes a Hopf bifurcation at $E^\ast$, producing periodic oscillations of the three populations.

Numerically, the non-sterile equilibrium is very sensitive to residual fertility $c$ within a narrow band, so small fertile contamination of releases can undermine suppression.

## Depends on

- [Hopf bifurcation of the delayed logistic equation](../hopf-bifurcation-of-the-delayed-logistic-equatio/README.md)

## Expansion

Substituting $\lambda=i\omega$ into the characteristic equation and separating real and imaginary parts gives two trigonometric equations whose elimination yields a polynomial equation in $\omega^2$; its positive roots $\omega_k$ determine the critical delays $\tau_k^{(j)}$ through the arccosine of an explicit ratio plus multiples of $2\pi/\omega_k$. Ruan's lemma on zeros of exponential polynomials ensures that roots can cross the imaginary axis only at these delays, so stability persists up to $\tau_0$. Implicit differentiation of the characteristic equation in $\tau$ gives $(d\lambda/d\tau)^{-1}$ explicitly, and evaluating its real part at $\lambda=i\omega_k$ shows that the crossing is from left to right, which is the transversality condition of the Hopf bifurcation theorem for retarded functional differential equations.

## Sources

- Ruqaya Hussein, Sergey Kryzhevich, Khosro Tajbakhsh, "Residual fertility and delay in sterile insect population dynamics", arXiv (2025). Section 2 (model (2.1)), Section 3 (equilibria, boundary equilibrium (3.2)), Section 4 (Theorem 1 and Lemmas 2–5 on stability), Section 5 (Theorem 6 transversality, Theorem 7 stability and Hopf bifurcation). <https://doi.org/10.48550/arXiv.2509.17519>
