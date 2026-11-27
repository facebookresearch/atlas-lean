# Delay-independent stability and Hopf bifurcation of the HPA axis model

**Setting.** Consider the four-dimensional distributed-delay HPA axis model and an equilibrium $E$ with cortisol level $x_0$ and receptor level $r_0$ (see the depends-on entry). Write $H_i(z)=\int_0^\infty e^{-zs}h_i(s)\,ds$ for the Laplace transforms of the kernels and set

$$
a=-w_2w_3\frac{x_0r_0f_2'(x_0r_0)}{f_2(x_0r_0)}>0,\qquad b=-w_1w_2w_3\frac{x_0f_1'(x_0)}{f_1(x_0)}>0,\qquad \tilde w_4=w_4-k_4x_0f_3'(x_0r_0)<w_4 .
$$

The characteristic equation of the linearization at $E$ is

$$
(z+w_1)(z+w_2)(z+w_3)(z+\tilde w_4)+a(w_4-\tilde w_4)(z+w_1)H_2H_{34}+b(z+\tilde w_4)H_1H_2H_{31}+a(z+w_1)(z+\tilde w_4)H_2H_{32}=0 .
$$

Introduce the conditions
$(I_0)$: $\tilde w_4>0$;
$(I_1)$: $(w_1+\tilde w_4)(w_2+\tilde w_4)(w_3+\tilde w_4)\ge(\tilde w_4-w_1)(\tilde w_4-w_4)(w_1+w_2+w_3+\tilde w_4)$;
$(I_2)$: $a(w_1+w_4)+b\le(w_1+w_2)(w_2+w_3)(w_1+w_3)$;
$(I_3)$: $a w_4/\tilde w_4+b/w_1<w_2w_3$, $(\overline{I_3})$ its negation $a w_4/\tilde w_4+b/w_1\ge w_2w_3$, and $(I_3^{>})$ the strict form $a w_4/\tilde w_4+b/w_1>w_2w_3$.

**Local stability.**
1. Without delays, $(I_0)$, $(I_1)$, $(I_2)$ imply that $E$ is locally asymptotically stable.
2. For arbitrary delay kernels, $(I_0)$ and $(I_3)$ imply that $E$ is locally asymptotically stable (delay-independent stability). Hence, under $(I_0)$, instability forces $(\overline{I_3})$.

**Hopf bifurcation.** Assume $H_{32}=H_{34}=H_1H_{31}$, so that the characteristic equation becomes $H(z)^{-1}=Q(z)$ with $H=H_2H_{32}$ (the transform of a kernel with total mean delay $\tau=\tau_2+\tau_{32}$) and

$$
Q(z)=-\frac{a(z+w_1)(z+w_4)+b(z+\tilde w_4)}{(z+w_1)(z+w_2)(z+w_3)(z+\tilde w_4)} .
$$

Under $(I_0)$, $\omega\mapsto|Q(i\omega)|$ is strictly decreasing on $[0,\infty)$, the equation $|Q(i\omega)|=1$ has a unique positive root $\omega_0$ exactly when $(I_3^{>})$ holds, and $\operatorname{Im}\big(Q'(i\omega)/Q(i\omega)\big)>0$ for $\omega>0$. The source's Lemma 2b states the root claim under the non-strict $(\overline{I_3})$; at equality $|Q(0)|=(aw_4/\tilde w_4+b/w_1)/(w_2w_3)=1$ and $|Q(i\omega)|<1$ for $\omega>0$, so there is no positive root and no Hopf point, and the page uses the strict form. Assume $(I_0)$, $(I_1)$, $(I_2)$ and $(I_3^{>})$.

- *Discrete delays* (all kernels Dirac, $H(z)=e^{-\tau z}$): with
$\tau_p=\big(\arccos[\operatorname{Re}Q(i\omega_0)]+2p\pi\big)/\omega_0$, $p\in\mathbb Z_+$, the equilibrium $E$ is asymptotically stable if and only if $\tau\in[0,\tau_0)$, and a Hopf bifurcation occurs at every $\tau=\tau_p$.
- *Gamma kernels* with common scale $\theta$ and integer shapes summing to $p\ge2$ along each loop ($H(z)=(\theta z+1)^{-p}$): let $\omega_p$ be the largest root in $(0,\omega_0)$ of

$$
T_p\Big(|Q(i\omega)|^{-1/p}\Big)=\frac{\operatorname{Re}Q(i\omega)}{|Q(i\omega)|},
$$

with $T_p$ the Chebyshev polynomial of the first kind, and set $\theta_p=\omega_p^{-1}\sqrt{|Q(i\omega_p)|^{2/p}-1}$. Then $E$ is asymptotically stable for $\theta\in(0,\theta_p)$ and the system undergoes a Hopf bifurcation at $\theta=\theta_p$.

The resulting limit cycles model the ultradian rhythm of the HPA axis; with two coexisting equilibria, two stable limit cycles can coexist for large mean delay.

## Expansion

Without delays the characteristic polynomial is a quartic with positive coefficients, and $(I_0)$–$(I_2)$ make the Routh–Hurwitz quantity $c_1c_2c_3-c_3^2-c_1^2c_4$ positive. With delays, $|H_i(z)|\le1$ on $\operatorname{Re}z\ge0$ and $|z+w|\ge w$ give $|\psi(z)|<|\varphi(z)|$ for the delay part $\psi$ and the polynomial part $\varphi$ whenever $(I_3)$ holds, so by Rouché's theorem no root enters the closed right half-plane. For the bifurcation, a purely imaginary root $i\omega$ requires $|H(i\omega)|^{-1}=|Q(i\omega)|$. For Dirac kernels this forces $\omega=\omega_0$ and $\cos(\omega\tau)=\operatorname{Re}Q(i\omega_0)$. For Gamma kernels, $|1+i\theta\omega|^p=|Q(i\omega)|$ fixes $\theta\omega$, and matching arguments $p\arctan(\theta\omega)=\arg Q(i\omega)$ produces the Chebyshev identity $\cos(p\phi)=T_p(\cos\phi)$ with $\cos\phi=|Q|^{-1/p}$. The sign of $\operatorname{Im}(Q'/Q)$ gives transversal crossing of the root pair.

## Depends on

- [Invariant box and equilibria of the four-dimensional HPA axis model](invariant-box-and-equilibria-of-the-hpa-axis-model.md)

## Sources

- E. Kaslik, M. Neamţu, "Stability and Hopf bifurcation analysis of a four-dimensional hypothalamic-pituitary-adrenal axis model with distributed delays", arXiv:1709.08936 (2017), Section 4 (Local stability analysis: characteristic equation and the theorem on local asymptotic stability) and Section 5 (Bifurcation analysis: the lemma on $Q$ and the Hopf bifurcation theorems for Dirac and Gamma kernels), <https://doi.org/10.48550/arXiv.1709.08936>.
