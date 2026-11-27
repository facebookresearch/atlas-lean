# Global attraction in the damped predator–prey model

**Model.** The "damped" Lotka–Volterra predator–prey system

$$\frac{dx}{dt} = \delta - \alpha x - \beta xy, \qquad \frac{dy}{dt} = \gamma xy - \sigma y,$$

with $\alpha, \beta, \gamma, \delta, \sigma > 0$, adds to the classical model ($\delta = \alpha = 0$, $\beta = \gamma$) a constant prey inflow $\delta$ and linear prey loss $\alpha$. The same equations describe target cells $x$ and infected cells $y$ in basic virus dynamics, susceptibles and infectives in SIR models with demography (Soper's model is $\alpha = 0$), and nutrient–hormone interactions in plant growth. The positive quadrant is invariant; the predator-free equilibrium is $(\delta/\alpha, 0)$.

**Theorem.** Suppose $\gamma\delta > \alpha\sigma$ (equivalently $\mathcal{R} = \frac{\gamma\delta}{\alpha\sigma} > 1$) and put $a = \frac{\gamma}{\sigma}\delta - \alpha > 0$. Then the coexistence equilibrium

$$p_* = \Big(\frac{\sigma}{\gamma},\ \frac{a}{\beta}\Big)$$

attracts every trajectory starting at $x_0, y_0 > 0$. As $\gamma\delta$ decreases through $\alpha\sigma$, $p_*$ merges with the predator-free equilibrium $(\delta/\alpha, 0)$ and leaves the positive quadrant: a bifurcation from damped oscillations to predator extinction.

## Proof sketch

Split the vector field as $X = X_0 + Z$ with the undamped Lotka–Volterra part $X_0 = (ax - \beta xy,\ \gamma xy - \sigma y)$ and the remainder $Z = (\delta - (\alpha + a)x,\ 0)$. The classical Volterra function

$$V(x,y) = \gamma x - \sigma\ln x + \beta y - a\ln y$$

is a first integral of $X_0$, so along $X$,

$$\dot V = \nabla V \cdot Z = -\frac{\gamma(a+\alpha)}{x}\Big(x - \frac{\sigma}{\gamma}\Big)\Big(x - \frac{\delta}{a+\alpha}\Big) = -\frac{\gamma(a+\alpha)}{x}\Big(x - \frac{\sigma}{\gamma}\Big)^2 \le 0,$$

because the choice of $a$ makes $\frac{\delta}{a+\alpha} = \frac{\sigma}{\gamma}$. By LaSalle's principle (limit points lie where $\dot V = 0$, i.e. on $x = \sigma/\gamma$, whose only invariant subset is $p_*$) and the properness of $V$ on the open quadrant, every positive trajectory converges to $p_*$. The analogy is with a damped harmonic oscillator: $V$ plays the role of energy, conserved for $X_0$ and dissipated by $Z$, and close to $p_*$ the approach is by damped oscillations.

## Sources

- Sergiy Koshkin and Isaiah Meyers, "Harmonic Oscillators of Mathematical Biology: Many Faces of a Predator-Prey Model", *Mathematics Magazine* 95 (2022), 172–187, <https://doi.org/10.1080/0025570x.2022.2055424>. Preprint version: arXiv:2206.09561 (2022), the damped model, Theorems 1–2 (Lyapunov function and global attraction) and the sections on predator extinction and virus dynamics, <https://doi.org/10.48550/arXiv.2206.09561>.
