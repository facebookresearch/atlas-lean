# Delay-induced Hopf bifurcation in the growth-factor hematopoiesis model

Consider the stem cell–mature cell–growth factor delay system with its positive steady state $(Q^*,M^*,E^*)$, which exists for $0\le\tau<\tau_{\max}$ (see the equilibria article below). Write $\beta'_1,\beta'_2$ for the partial derivatives of $\beta(Q,E)$ and set

$$
\begin{aligned}
A&=\delta+g'(Q^*)+\beta(Q^*,E^*)+\beta'_1(Q^*,E^*)Q^*, & B&=2e^{-\gamma\tau}\left[\beta(Q^*,E^*)+\beta'_1(Q^*,E^*)Q^*\right],\\
C&=\beta'_2(Q^*,E^*)Q^*, & D&=2e^{-\gamma\tau}\beta'_2(Q^*,E^*)Q^*,\\
G&=g'(Q^*), & H&=-f'(M^*),
\end{aligned}
$$

so that $C,D,G,H>0$ and all six coefficients depend on $\tau$ through the equilibrium. The linearisation about the positive steady state is

$$
q'=-Aq(t)+Bq(t-\tau)-Ce(t)+De(t-\tau),\qquad m'=-\mu m+Gq,\qquad e'=-ke-Hm .
$$

**Stability without delay.** At $\tau=0$ the positive steady state is locally asymptotically stable if and only if

$$
(\mu+k)\left[\mu k+(A-B)(\mu+k+A-B)\right]>GH(D-C).
$$

**Hopf bifurcation in the cell-cycle duration.** The characteristic equation has the form $P(\lambda,\tau)+Q(\lambda,\tau)e^{-\lambda\tau}=0$ with $P$ a monic cubic and $Q$ a quadratic in $\lambda$, both with $\tau$-dependent coefficients. Purely imaginary roots $i\omega$ require $F(\omega,\tau):=|P(i\omega,\tau)|^2-|Q(i\omega,\tau)|^2=h(\omega^2,\tau)=0$ with $h$ a cubic in $z=\omega^2$. Let $I\subset[0,\tau_{\max})$ be a set on which $h(\cdot,\tau)$ has a positive root $\omega^2(\tau)$, let $\theta(\tau)\in[0,2\pi)$ be the angle with $\cos\theta=-\operatorname{Re}(P/Q)$ and $\sin\theta=\operatorname{Im}(P/Q)$ evaluated at $(i\omega(\tau),\tau)$ (so that $e^{-i\theta}=-P/Q$, as $e^{-i\omega\tau}=-P/Q$ at a root), and define

$$
S_n(\tau)=\tau-\frac{\theta(\tau)+2n\pi}{\omega(\tau)},\qquad n\in\mathbb{N}.
$$

Assume that $\mu,k>0$, that the positive steady state exists, and that the $\tau=0$ stability inequality holds. Then:

1. If $S_0$ has no positive root in $I$, the positive steady state is locally asymptotically stable for every $\tau\ge0$ (in its existence range).
2. If $S_0$ has a positive root in $I$, there is $\tau^*\in I$ such that the steady state is locally asymptotically stable for $0\le\tau<\tau^*$ and unstable for $\tau\ge\tau^*$, with a Hopf bifurcation at $\tau=\tau^*$, if and only if $\partial h/\partial z\,(\omega^2(\tau^*),\tau^*)>0$.

## Expansion

At $\tau=0$ the characteristic polynomial is a cubic and the Routh–Hurwitz criterion yields the stated inequality. For $\tau>0$ the coefficients depend on $\tau$, so the classical delay-independent crossing analysis does not apply; instead one uses the Beretta–Kuang geometric criterion: $\pm i\omega(\tau^*)$ is a simple pair of imaginary roots exactly when $S_n(\tau^*)=0$, and the crossing direction satisfies $\operatorname{sign}\,\frac{d\operatorname{Re}\lambda}{d\tau}=\operatorname{sign}\,\frac{\partial h}{\partial z}\cdot\operatorname{sign}\,\frac{dS_n}{d\tau}$. Since $S_n(0)<0$ and $S_n>S_{n+1}$, if $S_0$ has no root none of the $S_n$ do; otherwise some root has $dS_n/d\tau>0$, giving a stability switch. Numerically, the resulting periodic solutions can have periods much longer than the cell-cycle duration, which the authors relate to periodic hematological diseases such as cyclical neutropenia.

## Depends on

- [Equilibria of the stem cell–growth factor delay model of hematopoiesis](equilibria-of-the-stem-cell-growth-factor-delay-model.md)

## Proof depends on

- [Routh–Hurwitz criterion for cubic polynomials](../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Sources

- M. Adimy, F. Crauste, S. Ruan, "Modelling hematopoiesis mediated by growth factors with applications to periodic hematological diseases", Section 3 (Proposition 3.2, Theorems 3.1 and 3.2) and Sections 4–5. <https://doi.org/10.48550/arXiv.0904.2501>
