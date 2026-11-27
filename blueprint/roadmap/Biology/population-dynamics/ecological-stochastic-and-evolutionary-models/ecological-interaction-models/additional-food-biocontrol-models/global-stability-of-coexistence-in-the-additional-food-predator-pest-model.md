# Global stability of coexistence in the additional-food predator–pest model

**Model.** A predator $y(t)$ with a Holling type II response hunts a pest $x(t)$ and is also supplied with additional food (AF) of quantity $\xi \ge 0$ and quality $1/\alpha > 0$:

$$\frac{dx}{dt} = x\left(1 - \frac{x}{\gamma}\right) - \frac{xy}{1 + \alpha\xi + x}, \qquad \frac{dy}{dt} = \frac{\beta (x + \xi)\, y}{1 + \alpha\xi + x} - \delta y,$$

with pest carrying capacity $\gamma > 0$, conversion rate $\beta > 0$ and predator death rate $\delta > 0$. Set

$$\hat\delta = \delta - \frac{\beta\xi}{1 + \alpha\xi},$$

the predator's effective death rate once the AF is accounted for at zero pest density.

**Theorem.** Suppose a positive coexistence equilibrium exists (so $\hat\delta > 0$) and $\beta > \hat\delta$. If

$$\gamma < \frac{(1 + \alpha\xi)(\beta + \hat\delta)}{\beta - \hat\delta},$$

then the coexistence equilibrium is globally asymptotically stable for positive initial data.

Because $(\beta + \hat\delta)/(\beta - \hat\delta) > 1$, this strictly improves the classical sufficient condition $\gamma < 1 + \alpha\xi$, which tied the admissible pest carrying capacity to the amount of AF supplied.

## Expansion

The predator equation is bounded above by the comparison system in which the AF term $\beta\xi/(1 + \alpha\xi + x)$ is replaced by its maximum $\beta\xi/(1 + \alpha\xi)$. That comparison system is a Rosenzweig–MacArthur model with half-saturation $1 + \alpha\xi$, conversion $\beta$ and death rate $\hat\delta$, whose interior equilibrium is globally stable when the carrying capacity lies left of the prey-isocline hump, $\gamma < (1 + \alpha\xi)(\beta + \hat\delta)/(\beta - \hat\delta)$. Sandwiching the AF model between this super-solution and the positive invariant region then rules out limit cycles and gives global attraction of the coexistence state. The condition is the drift-free ($q_1 = q_2 = 0$) special case of the single-patch global-stability theorem for the AF patch model.

## Sources

- Urvashi Verma, Aniket Banerjee and Rana D. Parshad, "T(w)o Patch or Not T(w)o Patch: A Novel Biocontrol Model", Mathematical Methods in the Applied Sciences 49 (2026), 14697–14743, <https://doi.org/10.1002/mma.70800>; numbering as in arXiv:2310.17003: Theorem 3 and Corollary 1 (Section 2).
