# Stability of the fast FitzHugh–Nagumo travelling pulse

For the FitzHugh–Nagumo equation $\partial_t w_1 = \partial_x^2 w_1 + f(w_1) - w_2$, $\partial_t w_2 = \epsilon(w_1 - \gamma w_2)$ with cubic $f(r) = r(r - a)(1 - r)$, where $0 < a < \tfrac12$ and $\epsilon, \gamma > 0$, take $\epsilon = 1/100$, $\gamma = 5$ and $a = 1/10$. Let $S$ be either the circle $\mathbb{R}/128\mathbb{Z}$ or the line $\mathbb{R}$, and let $\phi$ with speed $c$ be the corresponding pulse of [the existence statement](existence-of-travelling-pulse-solutions-of-the-fitzhugh-nagumo-equatio.md): the real-analytic $128$-periodic profile on the circle, and the profile homoclinic to the rest state, with $\phi(\pm\infty) = 0$, on the line.

Solutions are taken in the class of the source: a solution $w = (w_1, w_2)$ on $S \times [0, \infty)$ is bounded and uniformly continuous, and $\partial_x w_1$, $\partial_x^2 w_1$ and $\partial_x w_2$ are bounded and uniformly continuous. For such $w$ set $\delta(w, t, s) = \sup_{j, x} |w_j(x, t) - \phi_j(x - s - ct)|$, the supremum over $j \in \{1, 2\}$ and $x \in S$ (Eq. (1.6)). Stability is meant up to translation: $\phi$ is exponentially stable if there are $\alpha, b, C > 0$ such that for every $0 \le \beta \le b$ and every solution $w$ with $\delta(w, 0, 0) \le \beta$ there is a single shift $s \in [-C\beta, C\beta]$, depending on $w$, with $\delta(w, t, s) \le C\beta e^{-\alpha t}$ for all $t > 0$.

For these parameter values, Arioli and Koch prove that the periodic pulse on the circle (Theorem 1.1) and the homoclinic pulse on the line (Theorem 1.2) are each exponentially stable in this sense, by computer-assisted estimates. Both proofs reduce stability to excluding eigenvalues of the linearized generator from a closed right half-plane apart from the translation eigenvalue $0$. On the circle the eigenvalue problem is reduced by perturbation theory to estimates on finite matrices; on the line the number of eigenvalues in a small region is counted by estimating the Evans function on its boundary and applying the argument principle. This page states the stability results for these parameter values only.

The stability of the fast pulse for all sufficiently small $\epsilon > 0$ (Jones 1984; Yanagida 1985) and the instability of the slow pulse (Flores 1991), which Arioli and Koch recall in Section 1 without the hypotheses on $a$ and $\gamma$, are separate targets in the Expansion.

## Depends on

- [Existence of travelling pulses for the FitzHugh–Nagumo equations](../../../Biology/pattern-formation/travelling-pulses-in-nerve-models/existence-of-travelling-pulse-solutions-of-the-fitzhugh-nagumo-equatio.md)

## Proof depends on

- [Argument principle on a piecewise-smooth Jordan contour](../../../Analysis/complex-analysis/cauchy-theory/argument-principle/argument-principle-on-a-piecewise-smooth-jordan-contour.md)

## Expansion

1. The model and the pulse on each domain, whose [existence for these parameter values](../../../Biology/pattern-formation/travelling-pulses-in-nerve-models/existence-of-travelling-pulse-solutions-of-the-fitzhugh-nagumo-equatio.md) is stated there, and the solution class (bounded, uniformly continuous, with bounded uniformly continuous $\partial_x w_1$, $\partial_x^2 w_1$, $\partial_x w_2$).
2. The linearized operator about the pulse in a moving frame, the bound excluding its spectrum outside a small region near $0$, and the simple eigenvalue $0$ from translation invariance.
3. Circle: the reduction of the eigenvalue problem for the periodic pulse to finite matrix estimates, verified by computer.
4. Line: the Evans function of the homoclinic pulse, its computer-assisted estimates on the boundary of the small region, and the argument principle, showing that $0$ is the only eigenvalue in the closed right half-plane.
5. From linear stability to exponential stability modulo translation in the sense of Eq. (1.6), on each domain.
6. Separate targets: the stability of the fast pulse for small $\epsilon > 0$ by the singular-limit Evans-function argument of Jones (and Yanagida), and the instability of the slow pulse (Flores 1991), each with the hypotheses on $a$ and $\gamma$ recovered from the original papers.

## Sources

- G. Arioli and H. Koch, Existence and stability of traveling pulse solutions of the FitzHugh–Nagumo equation, Nonlinear Anal. 113 (2015), 51–70, Sections 1, 3 and 4, Eq. (1.6) and Theorems 1.1–1.2. <https://doi.org/10.1016/j.na.2014.09.023>
- Original result: C. K. R. T. Jones, Stability of the travelling wave solution of the FitzHugh–Nagumo system, Trans. Amer. Math. Soc. 286 (1984), 431–469. <https://doi.org/10.1090/s0002-9947-1984-0760971-6> The stability of the fast pulse for small $\epsilon$ follows Arioli and Koch, Section 1.
- Original result: E. Yanagida, Stability of fast travelling pulse solutions of the FitzHugh–Nagumo equations, J. Math. Biol. 22 (1985), 81–104. <https://doi.org/10.1007/BF00276548> Recalled by Arioli and Koch, Section 1, for the stability of the fast pulse for small $\epsilon$.
- Original result: G. Flores, Stability analysis for the slow traveling pulse of the FitzHugh–Nagumo system, SIAM J. Math. Anal. 22 (1991), 392–399. <https://doi.org/10.1137/0522025> Recalled by Arioli and Koch, Section 1, for the existence and instability of the slow pulse for small $\epsilon$.
