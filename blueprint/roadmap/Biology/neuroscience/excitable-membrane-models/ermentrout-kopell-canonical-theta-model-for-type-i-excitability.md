# The theta model of type I excitability

The theta model, or Ermentrout–Kopell canonical model, is the equation
$$\dot\theta = 1 - \cos\theta + (1 + \cos\theta)\, I, \qquad \theta \in S^1,$$
in which a spike is the passage of $\theta$ through $\pi$; it has a single saddle-node bifurcation and is the normal form of the saddle-node on a limit cycle (SNIC) bifurcation, derived by Ermentrout and Kopell (1986) through a change of coordinates under which a general parabolic bursting system converges to it away from $\theta = \pi$ (Wikipedia, Theta model, sections Model equations and properties and Derivation). For $I < 0$ the system is excitable, and for $I > 0$ every orbit is periodic. Explicitly, the fixed points solve $\tan^2(\theta/2) = -I$, so for $I < 0$ there are two of them, one stable and one unstable, which merge at $\theta = 0$ when $I = 0$. On $\theta \ne \pi$ the substitution $V = \tan(\theta/2)$ gives $\dot V = \frac{\dot\theta}{1 + \cos\theta} = V^2 + I$, the quadratic integrate-and-fire equation, with the passage through $\theta = \pi$ corresponding to escape of $V$ to $+\infty$ and reset to $-\infty$; hence for $I > 0$ the period is $\int_{-\infty}^{\infty} dV/(V^2 + I) = \pi/\sqrt I$, as stated in the source, and the frequency $\sqrt I/\pi$ tends to $0$ as $I \to 0^+$.

## Expansion

1. The model as a smooth vector field on the circle, its fixed points as functions of $I$, and the period for $I > 0$.
2. The conjugacy with the quadratic integrate-and-fire neuron, including the identification of spikes with passages through $\theta = \pi$.
3. The normal-form theorem of Ermentrout and Kopell: the hypotheses on a family undergoing a SNIC bifurcation and the sense (local coordinates, uniformity away from $\theta = \pi$) in which the theta model is its normal form, fixed from the 1986 paper.
4. The scaling law of the frequency near the bifurcation, and the phase response curve $1 + \cos\theta$, as separate statements.

## Sources

- Theta model, Wikipedia, sections Model equations and properties, Derivation and Quadratic integrate-and-fire. <https://en.wikipedia.org/wiki/Theta_model>
- Original result: G. B. Ermentrout and N. Kopell, Parabolic bursting in an excitable system coupled with a slow oscillation, SIAM J. Appl. Math. 46 (1986), 233–253. <https://doi.org/10.1137/0146017> The normal-form statement follows the Wikipedia article on the theta model.
