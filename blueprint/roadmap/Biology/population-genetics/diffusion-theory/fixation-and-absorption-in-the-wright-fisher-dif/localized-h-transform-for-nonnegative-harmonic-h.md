# Localized h-transform for a nonnegative harmonic function: conditioning on fixation

Let $\alpha \in \mathbb R$, let $X$ solve the [martingale problem for the Wright–Fisher diffusion](is-wright-fisher-solution.md) with generator $L f = \tfrac12 x(1-x) f'' + \alpha x(1-x) f'$, without mutation, with $X_0 = p \in (0, 1)$, and let $h = u_\alpha$ be the [fixation probability](measure-real-fixation.md), so that $L h = 0$, $h(0) = 0$ and $h(1) = 1$. Since $h(0) = 0$, the exponential tilt by $h$ is localized away from $0$:

- for $\varepsilon \in (0, p)$ choose $h_\varepsilon \in C^2[0, 1]$ with $h_\varepsilon \ge c_\varepsilon > 0$ on $[0, 1]$ and $h_\varepsilon = h$ on $[\varepsilon, 1]$, and let $\tau_\varepsilon$ be the [hitting time](../../../../Probability/markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/hitting-times-of-closed-sets-by-continuous-adapt.md) of $[0, \varepsilon]$;
- the [martingale problem under exponential tilt](../../../../Probability/markov-chains/martingale-problems/martingale-problem-under-exponential-tilt-generi.md) applied to $h_\varepsilon$ and stopped at $\tau_\varepsilon$ has density $Z_{t \wedge \tau_\varepsilon} = h(X_{t \wedge \tau_\varepsilon})/h(p)$, because $L h_\varepsilon / h_\varepsilon = 0$ on $[\varepsilon, 1]$; under the tilted measure the stopped process solves the martingale problem for $L + x(1-x)\frac{h'(x)}{h(x)} \frac{d}{dx}$ up to $\tau_\varepsilon$.

Letting $\varepsilon \to 0$, the tilted measures are $\mathbb P(\,\cdot \mid \text{fixation})$, and the conditioned process does not hit $0$. In the neutral case $h(x) = x$ and the tilted drift is $1 - x$.

## Depends on

- [Martingale problem under exponential tilt (generic)](../../../../Probability/markov-chains/martingale-problems/martingale-problem-under-exponential-tilt-generi.md)
- [Hitting times of closed sets by continuous adapted processes are stopping times (continuous time)](../../../../Probability/markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/hitting-times-of-closed-sets-by-continuous-adapt.md)
- [Kimura's fixation probability, process form](measure-real-fixation.md)
- [Martingale problem for the Wright–Fisher diffusion](is-wright-fisher-solution.md)

## Proof depends on

- [Optional stopping theorem in continuous time](../../../../Probability/martingales/optional-stopping-theorem/stopped-value-ae-eq-cond-exp-of-le-of-co.md)

## Expansion

A full proof page must still establish:

- the existence of the positive extensions $h_\varepsilon$ and the identity $Z_{t \wedge \tau_\varepsilon} = h(X_{t \wedge \tau_\varepsilon})/h(p)$;
- that the tilted probability of $\{\tau_\varepsilon < \infty\}$ tends to $0$ as $\varepsilon \to 0$, and the identification of the limit with conditioning on fixation, by optional stopping;
- the neutral case.

## Sources

- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer, 2004, Chapter 4 (conditioned diffusions), <https://doi.org/10.1007/978-0-387-21822-9>
- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press, 1981, Chapter 15 (conditioned processes)
