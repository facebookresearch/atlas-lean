# Value function of the SIR eradication-time problem

Let $\beta, \gamma > 0$ and a threshold $\mu > 0$. Consider the vaccination-controlled SIR system

$$\dot S = -\beta S I - r(t) S, \qquad \dot I = \beta S I - \gamma I,$$

with admissible controls $\mathcal{A} = \{ r \in L^\infty([0,\infty)) : 0 \le r(t) \le 1 \text{ for a.e. } t \}$. For every $r \in \mathcal{A}$ and $S(0) = x \ge 0$, $I(0) = y \ge 0$ there is a unique Lipschitz solution $(S^r, I^r)$, and if $I(0) > 0$ then $\lim_{t\to\infty} S^r(t) \in [0, \gamma/\beta)$ exists and $I^r(t) \to 0$. Hence the **eradication time**

$$u^r(x,y) = \inf\{ t > 0 : I^r(t) = \mu \}, \qquad x \ge 0,\ y \ge \mu,$$

is finite, and the value function is $u(x,y) = \min_{r \in \mathcal{A}} u^r(x,y)$.

**Theorem.**

1. (Existence) There is $r^* \in \mathcal{A}$ with $u^{r^*} \le u^r$ for all $r \in \mathcal{A}$; at any time the trajectory hits the threshold, $\beta S < \gamma$.
2. (Dynamic programming) For $t \in [0, u(x,y)]$, $u(x,y) = \min_{r \in \mathcal{A}} \{ t + u(S^r(t), I^r(t)) \}$.
3. (Characterization) $u$ is the unique continuous viscosity solution in $(0,\infty) \times (\mu, \infty)$ of the Hamilton–Jacobi–Bellman equation

$$\beta x y\, \partial_x u + x (\partial_x u)^+ + (\gamma - \beta x) y\, \partial_y u = 1$$

satisfying the boundary conditions $u(x,\mu) = 0$ for $0 \le x \le \gamma/\beta$, $u(0,y) = \gamma^{-1} \ln(y/\mu)$ for $y \ge \mu$, and $u(x,y) \to \infty$ as $x + y \to \infty$.
4. (Semiconcavity) For each convex compact $K \subset (0,\infty) \times (\mu,\infty)$ there is $L$ such that $u(x,y) - \tfrac{L}{2}(x^2+y^2)$ is concave on $K$; in particular $u$ is twice differentiable almost everywhere.

The value function also obeys the explicit bounds $\dfrac{\ln(x+y) - \ln(\gamma/\beta + \mu)}{\max\{\gamma, 1\}} \le u(x,y) \le \dfrac{x+y}{\mu\gamma}$.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

Existence follows from weak-* compactness of $\mathcal{A}$ in $L^\infty$: solutions depend continuously on weak-* convergent controls (the control enters linearly), and the hitting time is continuous along such sequences because $\dot I = (\beta S - \gamma) I < 0$ at the hitting time. The identity $u^r(x,y) = t + u^r(S^r(t), I^r(t))$ gives the dynamic programming principle, and the standard argument turns it into the viscosity HJB equation, where the term $x(\partial_x u)^+ = \max_{0 \le r \le 1}( r x \partial_x u)$ is the Hamiltonian contribution of the control. On the axis $x = 0$ the infected class decays like $y e^{-\gamma t}$, giving the explicit boundary datum. Uniqueness is proved through the Kruzkov transform $v = e^{-u}$, which turns the equation into the proper equation $v + \beta x y\, \partial_x v - x(\partial_x v)^- + (\gamma - \beta x) y\, \partial_y v = 0$, and a comparison principle for it; semiconcavity comes from uniform second-derivative bounds on $u^r$ for smooth controls, using non-degeneracy $\gamma - \beta S \ge \varepsilon$ at the hitting time.

## Sources

- Ryan Hynd, Dennis Ikpe, Terrance Pendleton, "An eradication time problem for the SIR model", arXiv (2020). Theorem 1.2, Theorem 1.3, Lemma 2.1, Lemma 2.2, Corollary 2.3, Theorem 2.5, Lemma 3.1, Proposition 3.4, Lemma 3.6. <https://doi.org/10.48550/arXiv.2008.12744> Published version: Journal of Differential Equations 303 (2021) 214–252, <https://doi.org/10.1016/j.jde.2021.09.001>.
