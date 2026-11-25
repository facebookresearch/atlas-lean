# The optimal Berry–Esseen constant

Call a real number $C$ admissible if for every probability measure $\mu$ on $\mathbb{R}$ with mean
$0$, variance $1$ and finite third absolute moment $\rho = \int |x|^3 \, d\mu$, and every positive
integer $n$,

$$\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le \frac{C \rho}{\sqrt{n}},$$

where $F_n$ is the distribution function of $(X_1 + \dots + X_n)/\sqrt{n}$ for independent random
variables $X_1, X_2, \dots$ with law $\mu$, and $\Phi$ is the standard normal distribution function.
The optimal Berry–Esseen constant $C_0$ is the infimum of the admissible $C$. It is a real number:
$42$ is admissible, and every admissible constant is nonnegative.

## Idea

The Berry–Esseen theorem says that some admissible constant exists; $C_0$ is the best one for
identically distributed summands, a single number that records the worst case over all laws and all
$n$. The admissible constants form an upward closed set, and since admissibility is a family of
non-strict inequalities, $C_0$ is itself admissible: it is the least admissible constant, and a
constant is admissible exactly when it is at least $C_0$. Its exact value is unknown. Esseen showed
$C_0 \ge (\sqrt{10} + 3)/(6\sqrt{2\pi}) \approx 0.4097$, and a long series of improvements has brought
the upper bound down to $0.4748$ (Shevtsova, 2011). A technical point: measuring the error with $P(S_n/\sqrt{n} < x)$ instead
of $P(S_n/\sqrt{n} \le x)$ gives the same supremum, because $\Phi$ is continuous.

## Statements

- [The optimal Berry–Esseen constant](value.md)
- [Admissible Berry–Esseen coefficient](is-admissible.md): definition used in the main definition
- [Admissible coefficients are nonnegative](is-admissible-nonnegative.md): basic property of admissible coefficients
- [Admissibility is upward closed](is-admissible-mono.md): basic property: admissibility is upward closed
- [Admissible Berry–Esseen coefficients exist](admissible-nonempty.md): lemma: the infimum is over a nonempty set
- [The admissible Berry–Esseen coefficients are bounded below](admissible-bdd-below.md): lemma: the infimum is over a set bounded below
- [The Berry–Esseen bound with coefficient 42](is-admissible-forty-two.md): the coefficient 42 is admissible
- [The optimal Berry–Esseen coefficient is nonnegative](value-nonnegative.md): basic property of the constant
- [The optimal Berry–Esseen coefficient is at most every admissible one](value-le-of-is-admissible.md): basic property of the infimum
- [The optimal Berry–Esseen coefficient is at most 42](value-le-forty-two.md): crude upper bound 42
- [The optimal Berry–Esseen coefficient satisfies the Berry–Esseen bound](value-bound.md): the constant itself satisfies the Berry–Esseen bound
- [The optimal Berry–Esseen coefficient is admissible](value-is-admissible.md): restatement of the bound as admissibility
- [The Berry–Esseen constant is the least admissible coefficient](value-is-least.md): characterisation: the least admissible coefficient
- [Admissible coefficients are exactly those above the optimal one](is-admissible-iff-value-le.md): characterisation of admissible coefficients
- [Admissible coefficients bound every standardized i.i.d. sequence](iid-bound.md): restatement for i.i.d. random variables
- [Statement of the Kolmogorov distance via left-continuous distribution functions](left-right-cdferror-equivalence.md): statement: Kolmogorov distance via left-continuous CDFs
- [Kolmogorov distance via left-continuous distribution functions](left-right-cdferror-equivalence-holds.md): the equality of the two suprema

## Background

- [Berry–Esseen theorem](../../berry-esseen-theorem/berry-esseen-bound/README.md): the inequality
  whose best constant is studied here.
- [Kolmogorov distance to the normal law](../../berry-esseen-theorem/kolmogorov-distance/README.md):
  the error measured on the left-hand side.
