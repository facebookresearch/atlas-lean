# Identification of vaccine effects conditional on unmeasured exposure

**Setting.** In a trial, $A \in \{0, 1\}$ is vaccine assignment, $E \in \{0, 1\}$ indicates exposure to
the infectious agent (unmeasured), and $Y$ is the outcome (for example symptomatic disease), with
counterfactuals $E^{a}, Y^{a}$ under assignment $a$. The **causal effect conditional on exposure** (CECE)
contrasts $E(Y^{a=1} \mid E = 1)$ with $E(Y^{a=0} \mid E = 1)$.

**Assumptions.**

- No effect on exposure: $E^{a=1} = E^{a=0}$ (plausible in a blinded trial), so $E = E^{a}$ for both $a$.
- Treatment exchangeability $(Y^{a}, E^{a}) \perp A$, positivity $P(A = a) > 0$, and consistency
  ($A = a \Rightarrow E = E^{a}, Y = Y^{a}$); all hold by randomization.
- Exposure necessity: $E^{a} = 0 \Rightarrow Y^{a} = 0$ for both $a$.

**Proposition (relative CECE).** Under these assumptions and $E(Y \mid A = 0) > 0$,

$$\frac{E(Y^{a=1} \mid E = 1)}{E(Y^{a=0} \mid E = 1)} = \frac{E(Y \mid A = 1)}{E(Y \mid A = 0)}:$$

the usual trial risk ratio is the risk ratio among the exposed, and also the relative principal
stratum effect among those exposed under either assignment.

**Proposition (sharp bounds on the absolute CECE).** For $Y \in [0, 1]$ and
$E(Y \mid A = 0) \ge E(Y \mid A = 1)$,

$$E(Y \mid A = 0) - E(Y \mid A = 1) \le E(Y^{a=0} \mid E = 1) - E(Y^{a=1} \mid E = 1) \le 1 - \frac{E(Y \mid A = 1)}{E(Y \mid A = 0)},$$

and these bounds are sharp: the lower bound is the risk difference (attained when everyone is exposed)
and the upper bound is the conventional vaccine efficacy (attained when unvaccinated individuals have
the outcome exactly when exposed).

**Proposition (point identification with external data).** Under the same assumptions,

$$E(Y^{a=0} \mid E = 1) - E(Y^{a=1} \mid E = 1) = E(Y \mid E = 1, A = 0)\Bigl(1 - \frac{E(Y \mid A = 1)}{E(Y \mid A = 0)}\Bigr) = \frac{E(Y \mid A = 0) - E(Y \mid A = 1)}{P(E = 1 \mid A = 0)},$$

so external knowledge of the attack risk among exposed unvaccinated people, or of the exposure
probability, identifies the absolute effect.

## Expansion

Exposure necessity gives $E(Y \mid A = a) = P(E = 1 \mid A = a)\,E(Y \mid E = 1, A = a)$, and no effect on
exposure with randomization makes $P(E = 1 \mid A = a) = P(E = 1)$ the same in both arms. The unknown
exposure probability cancels in the ratio but not in the difference, which is why only relative
effects are point identified. Writing the absolute CECE as $E(Y \mid A{=}0, E{=}1)$ times one minus the
risk ratio and letting $E(Y \mid A = 0, E = 1)$ range over $[E(Y \mid A = 0), 1]$ yields the bounds. This
mirrors the classical fact that an outcome measured with perfect specificity still gives unbiased risk
ratios.

## Sources

- M. J. Stensrud, L. Smith, "Identification of vaccine effects when exposure status is unknown",
  Epidemiology 34 (2023), assumptions (5) and (7)-(10) and Propositions 1-3,
  <https://doi.org/10.1097/ede.0000000000001573> (PMC9891279).
