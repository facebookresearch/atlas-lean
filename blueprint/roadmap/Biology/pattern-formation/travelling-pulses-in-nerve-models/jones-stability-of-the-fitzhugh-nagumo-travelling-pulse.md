# Stability of the fast FitzHugh–Nagumo travelling pulse

For the FitzHugh–Nagumo equation $\partial_t w_1 = \partial_x^2 w_1 + f(w_1) - w_2$, $\partial_t w_2 = \epsilon(w_1 - \gamma w_2)$ with cubic $f(r) = r(r - a)(1 - r)$, where $0 < a < \tfrac12$ and $\epsilon, \gamma > 0$, take $\epsilon = 1/100$, $\gamma = 5$ and $a = 1/10$. Stability is meant up to translation: a pulse $\phi$ with speed $c$ is exponentially stable if there are $\alpha, b, C > 0$ such that every solution $w$ starting within $\beta \le b$ of $\phi$ in the supremum norm stays within $C\beta e^{-\alpha t}$ of a translate $\phi(\cdot - s - ct)$ with $|s| \le C\beta$ (Eq. (1.6) and the definition after it). For these parameter values, Arioli and Koch prove that the travelling pulse of [the existence statement](existence-of-travelling-pulse-solutions-of-the-fitzhugh-nagumo-equatio.md) is exponentially stable in this sense, by computer-assisted estimates that include estimates on the Evans function (Theorems 1.1 and 1.2). This page states the stability result for these parameter values only.

The stability of the fast pulse for all sufficiently small $\epsilon > 0$ (Jones 1984; Yanagida 1985) and the instability of the slow pulse (Flores), which Arioli and Koch recall in Section 1 without the hypotheses on $a$ and $\gamma$, are separate targets in the Expansion.

## Depends on

- [Existence of travelling pulses for the FitzHugh–Nagumo equations](../../../Biology/pattern-formation/travelling-pulses-in-nerve-models/existence-of-travelling-pulse-solutions-of-the-fitzhugh-nagumo-equatio.md)

## Expansion

1. The model and the pulse, whose [existence for these parameter values](../../../Biology/pattern-formation/travelling-pulses-in-nerve-models/existence-of-travelling-pulse-solutions-of-the-fitzhugh-nagumo-equatio.md) is stated there.
2. The linearized operator about the pulse in a moving frame, its essential spectrum in a left half-plane, and the simple eigenvalue $0$ from translation invariance.
3. The Evans function and its computer-assisted estimates for $\epsilon = 1/100$, $\gamma = 5$, $a = 1/10$, showing that no other eigenvalue lies in the closed right half-plane.
4. From linear stability to exponential stability modulo translation in the sense of Eq. (1.6).
5. Separate targets: the stability of the fast pulse for small $\epsilon > 0$ by the singular-limit Evans-function argument of Jones (and Yanagida), and the instability of the slow pulse (Flores), each with the hypotheses on $a$ and $\gamma$ recovered from the original papers.

## Sources

- G. Arioli and H. Koch, Existence and stability of traveling pulse solutions of the FitzHugh–Nagumo equation, Nonlinear Anal. 113 (2015), 51–70, Section 1, Eq. (1.6) and Theorems 1.1–1.2. <https://doi.org/10.1016/j.na.2014.09.023>
- Original result: C. K. R. T. Jones, Stability of the travelling wave solution of the FitzHugh–Nagumo system, Trans. Amer. Math. Soc. 286 (1984), 431–469. <https://doi.org/10.1090/s0002-9947-1984-0760971-6> The stability of the fast pulse for small $\epsilon$ follows Arioli and Koch, Section 1.
