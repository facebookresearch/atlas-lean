# Gamma-Gompertz-Makeham frailty hazard

**Model.** The Gompertz–Makeham hazard at age $x \ge 0$ is $\mu(x) = a e^{bx} + c$ with $a, b > 0$ and $c \ge 0$. In the gamma-Gompertz–Makeham ($\Gamma$GM) model each individual carries a frailty $z > 0$, fixed for life, acting proportionally on the age-dependent part:

$$\mu(x, z) = z\, a e^{bx} + c,$$

and at the starting age frailty is gamma distributed, $Z \sim \Gamma(\kappa, \lambda)$ with mean $\kappa/\lambda$ and variance $\kappa/\lambda^2$. Normalizing $E(Z) = 1$ forces $\lambda = \kappa$ and leaves one heterogeneity parameter $\gamma = V(Z) = 1/\lambda$.

**Proposition (marginal hazard).** The hazard of the cohort as a whole, averaging over surviving frailties, is the sigmoid

$$\bar\mu(x) = \frac{a e^{bx}}{1 + \frac{a\gamma}{b}\big(e^{bx} - 1\big)} + c,$$

with $\bar\mu(0) = a + c$. For $\gamma > 0$ its derivative has the sign of $b - a\gamma$: if $b > a\gamma$ the hazard rises and levels off at the finite plateau $b/\gamma + c$ as $x \to \infty$; if $b = a\gamma$ it is constant, equal to $a + c$; and if $b < a\gamma$ it decreases from $a + c$ to $b/\gamma + c$. For example $a = 2$, $b = \gamma = 1$, $c = 0$ gives a hazard falling from $2$ to $1$. With $\gamma = 0$ (a homogeneous cohort) it reduces to the Gompertz–Makeham hazard $a e^{bx} + c$, which has no plateau. Parameters $a, b, c, \gamma$ are estimated by maximum likelihood from cohort deaths and exposures using $\bar\mu$.

## Proof depends on

- [Laplace transform of the gamma density](../../../../Probability/distributions/continuous/gamma-distribution/gamma-mgf/lintegral-gamma-pdf-mul-exp.md)

## Expansion

Survival of an individual with frailty $z$ is $\exp\{-z H(x) - cx\}$ with cumulative baseline $H(x) = \tfrac ab (e^{bx}-1)$. The gamma Laplace transform gives population survival $e^{-cx}(1 + \gamma H(x))^{-1/\gamma}$, and differentiating its logarithm gives the marginal hazard above. Writing $u = e^{bx}$, the age-dependent part is $a u/\bigl(1 - a\gamma/b + (a\gamma/b) u\bigr)$, whose derivative in $u$ is $a(1 - a\gamma/b)$ divided by the squared denominator, which gives the sign of $b - a\gamma$. The plateau reflects selection within the cohort: frail individuals die first, so mean frailty among survivors falls as $1/(1 + \gamma H(x))$, a mechanism proposed for the late-life mortality deceleration seen in human data. Discretizing $Z$ into $g$ classes with frailties $z_i$ gives class-specific mortality vectors $\mu_i = z_i \mu_0 + c$ over $\omega$ age classes, the input to an age × frailty matrix model.

## Sources

- N. Hartemink, T. I. Missov, H. Caswell, "Stochasticity, heterogeneity, and variance in longevity in human populations", Theoretical Population Biology 114:107–116 (2017), Section 2 (Eqs 1–3) and Section 3 (Eqs 4–5), <https://doi.org/10.1016/j.tpb.2017.01.001>, PMCID PMC5336383.
