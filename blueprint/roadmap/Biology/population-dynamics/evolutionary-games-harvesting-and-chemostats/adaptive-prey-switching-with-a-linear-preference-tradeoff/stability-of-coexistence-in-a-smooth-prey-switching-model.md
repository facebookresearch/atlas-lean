# Stability of coexistence in a smooth prey-switching model

**Model.** A predator $z$ feeds adaptively on a preferred prey $p_1$ and an alternative, defended prey $p_2$ with Lotka–Volterra interactions. The predator's switch between diets is smoothed by a hyperbolic tangent of steepness $k > 0$ across the switching line $p_1 = a_q p_2$, where $a_q > 0$ is the slope of a linear preference tradeoff:

$$
\begin{aligned}
\dot p_1 &= r_1 p_1 - p_1 z\, \frac{1 + \tanh(k(p_1 - a_q p_2))}{2},\\
\dot p_2 &= r_2 p_2 - p_2 z\, \frac{1 - \tanh(k(p_1 - a_q p_2))}{2},\\
\dot z &= e q_1 p_1 z\, \frac{1 + \tanh(k(p_1 - a_q p_2))}{2} + e q_2 p_2 z\, \frac{1 - \tanh(k(p_1 - a_q p_2))}{2} - m z,
\end{aligned}
$$

with prey growth rates $r_1 > r_2 > 0$, predator death rate $m > 0$, conversion efficiency $e > 0$ and diet benefits $0 < q_2 < q_1 < 1$. As $k \to \infty$ this recovers the piecewise-smooth (Filippov) model in which the predator eats only $p_1$ when $p_1 > a_q p_2$ and only $p_2$ otherwise.

**Coexistence state.** There is a unique steady state with $\tilde z = r_1 + r_2$ and

$$
\tilde p_1 = \frac{a_q m (r_1 + r_2) + \frac{e q_2 r_2}{k}\,\mathrm{arctanh}\frac{r_1 - r_2}{r_1 + r_2}}{e(q_1 a_q r_1 + q_2 r_2)}, \qquad \tilde p_2 = \frac{m (r_1 + r_2) - \frac{e q_1 r_1}{k}\,\mathrm{arctanh}\frac{r_1 - r_2}{r_1 + r_2}}{e(q_1 a_q r_1 + q_2 r_2)},
$$

and all three densities are positive exactly when

$$
k > k_0 = \frac{e q_1 r_1\, \mathrm{arctanh}\frac{r_1 - r_2}{r_1 + r_2}}{m (r_1 + r_2)} .
$$

**Proposition 2.1.** If $a_q \ge q_2/q_1$ (steep tradeoff), the coexistence state is stable if and only if $k > k_0$.

**Proposition 2.2.** If $a_q < q_2/q_1$ (shallow tradeoff), there is $k_1 \in (k_0, \infty)$, given explicitly in the paper, such that the coexistence state is stable if and only if $k \in (k_0, k_1)$.

## Expansion

At the steady state the two prey equations force the predator's effective attack on each prey to equal that prey's growth rate, which fixes $\tilde z = r_1 + r_2$ and $\tanh(k(\tilde p_1 - a_q \tilde p_2)) = (r_1 - r_2)/(r_1 + r_2)$; together with the predator equation this gives a linear system for $(\tilde p_1, \tilde p_2)$. Stability follows from the Routh–Hurwitz conditions for the cubic characteristic polynomial of the Jacobian. As $k \to \infty$ the state tends to the pseudo-equilibrium of the Filippov model on the switching line, which is stable for $a_q > q_2/q_1$ and repelling for $a_q < q_2/q_1$. The smooth model thus agrees with the discontinuous one for steep switching, but for shallow tradeoffs it adds a window of intermediate switching steepness in which coexistence is stable. Fitted to Lake Constance ciliate–algae data by approximate Bayesian computation, the model fits best with steep switching.

## Depends on

- [Lotka–Volterra predator–prey model](../../lotka-volterra-predator-prey-model/README.md)

## Sources

- Sofia H. Piltz, Lauri Harhanen, Mason A. Porter, Philip K. Maini, "Inferring parameters of prey switching in a 1 predator–2 prey plankton system with a linear preference tradeoff", Journal of Theoretical Biology 456 (2018), 108–122, <https://doi.org/10.1016/j.jtbi.2018.07.005>. Published version of arXiv:1610.07094, cited next; locators there refer to the arXiv version.
- Sofia H. Piltz, Lauri Harhanen, Mason A. Porter, Philip K. Maini, "Inferring parameters of prey switching in a plankton 1 predator–2 prey system with a linear preference tradeoff," arXiv 2016. Section 2.1 (smooth model I, coexistence steady state, threshold $k_0$), Propositions 2.1 and 2.2, Appendix A. <https://doi.org/10.48550/arXiv.1610.07094>
