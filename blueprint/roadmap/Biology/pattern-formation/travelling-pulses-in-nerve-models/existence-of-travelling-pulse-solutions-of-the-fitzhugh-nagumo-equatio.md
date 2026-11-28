# Existence of travelling pulses for the FitzHugh–Nagumo equations

Consider the FitzHugh–Nagumo equation

$$\partial_t w_1 = \partial_x^2 w_1 + f(w_1) - w_2, \qquad \partial_t w_2 = \epsilon(w_1 - \gamma w_2), \qquad f(r) = r(r - a)(1 - r),\ 0 < a < \tfrac12,\ \epsilon, \gamma > 0$$

(Arioli and Koch 2015, Eqs. (1.1)–(1.2)). A travelling wave $w_j(x, t) = \phi_j(x - ct)$ satisfies the profile equations $\phi_1'' + c\phi_1' = -f(\phi_1) + \phi_2$, $c\phi_2' = -\epsilon(\phi_1 - \gamma\phi_2)$ (Eq. (1.4)). The two domains give two different kinds of pulse, and a nonconstant periodic profile cannot tend to the rest state at infinity, so they are stated separately. Fix the parameter values $\epsilon = 1/100$, $\gamma = 5$ and $a = 1/10$.

1. Periodic pulse (Theorem 1.1). On the circular axon $\mathbb{R}/128\mathbb{Z}$, the equation has a travelling wave whose profile $\phi = (\phi_1, \phi_2)$ is a nonconstant, real-analytic, $128$-periodic solution of Eq. (1.4), with speed $c = 0.470336308\ldots$; equivalently, the first-order system (1.5) has a periodic orbit of period $128$. Arioli and Koch call it a traveling pulse because it has a single localized peak per period; it is not homoclinic.
2. Pulse on the line (Theorem 1.2). On $\mathbb{R}$, the equation has a travelling pulse with speed $c = 0.470336270\ldots$: a nonconstant real-analytic solution of Eq. (1.4) with $\phi_j(\pm\infty) = 0$, that is, an orbit of (1.5) homoclinic to the rest state, and $\phi$ decreases exponentially at infinity.

Both proofs use computer-assisted estimates. This page states the existence results for these parameter values only.

The perturbative existence results for small $\epsilon > 0$, for the fast pulse by Hastings (1976) and Carpenter (1977) and for the slow pulse by Flores (1991), which Arioli and Koch recall in Section 1 without their hypotheses on $a$ and $\gamma$, are not part of this statement; they are separate targets in the Expansion.

## Expansion

1. The model and the travelling-wave system, with the conditions on $f$, $a$, $\gamma$ under which the rest state is the only equilibrium.
2. The singular limit $\epsilon = 0$: the fast front and back (heteroclinic orbits of the fast subsystem) joined by slow segments.
3. Separate target: persistence of a homoclinic orbit for small $\epsilon > 0$, by Hastings's shooting argument or by geometric singular perturbation theory (Carpenter), with the hypotheses on $a$ and $\gamma$ recovered from the original papers.
4. The slow pulse and periodic wave trains, as separate statements.
5. The computer-assisted proof of Arioli and Koch for $\epsilon = 1/100$, $\gamma = 5$, $a = 1/10$, the statement of this page, and the [stability of the fast pulse](../../../Biology/pattern-formation/travelling-pulses-in-nerve-models/jones-stability-of-the-fitzhugh-nagumo-travelling-pulse.md).

## Sources

- G. Arioli and H. Koch, Existence and stability of traveling pulse solutions of the FitzHugh–Nagumo equation, Nonlinear Anal. 113 (2015), 51–70, Section 1 and Theorems 1.1–1.2. <https://doi.org/10.1016/j.na.2014.09.023>
- Original result: S. P. Hastings, On the existence of homoclinic and periodic orbits for the FitzHugh–Nagumo equations, Quart. J. Math. Oxford (2) 27 (1976), 123–134. <https://doi.org/10.1093/qmath/27.1.123> Existence of the fast pulse for small $\epsilon$ follows Arioli and Koch, Section 1.
- Original result: G. A. Carpenter, A geometric approach to singular perturbation problems with applications to nerve impulse equations, J. Differential Equations 23 (1977), 335–367. <https://doi.org/10.1016/0022-0396(77)90116-4> Existence of the fast pulse for small $\epsilon$ follows Arioli and Koch, Section 1.
- Original result: G. Flores, Stability analysis for the slow traveling pulse of the FitzHugh–Nagumo system, SIAM J. Math. Anal. 22 (1991), 392–399. <https://doi.org/10.1137/0522025> Recalled by Arioli and Koch, Section 1, for the existence and instability of the slow pulse for small $\epsilon$.
