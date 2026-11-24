# Existence of travelling pulses for the FitzHugh–Nagumo equations

Consider the FitzHugh–Nagumo equation

$$\partial_t w_1 = \partial_x^2 w_1 + f(w_1) - w_2, \qquad \partial_t w_2 = \epsilon(w_1 - \gamma w_2), \qquad f(r) = r(r - a)(1 - r),\ 0 < a < \tfrac12,\ \epsilon, \gamma > 0$$

(Arioli and Koch 2015, Eqs. (1.1)–(1.2)). A travelling wave $w_j(x, t) = \phi_j(x - ct)$ satisfies a system of ordinary differential equations, and a travelling pulse is a solution of this system homoclinic to the rest state.

For the parameter values $\epsilon = 1/100$, $\gamma = 5$ and $a = 1/10$, Arioli and Koch prove, with computer-assisted estimates, that the equation has a real-analytic travelling pulse on a circular axon of length $128$ (Theorem 1.1) and on the line (Theorem 1.2). This page states the existence result for these parameter values only.

The perturbative existence results for small $\epsilon > 0$, for the fast pulse by Hastings (1976) and Carpenter (1977) and for the slow pulse by Flores, which Arioli and Koch recall in Section 1 without their hypotheses on $a$ and $\gamma$, are not part of this statement; they are separate targets in the Expansion.

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
