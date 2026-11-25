# Berry–Esseen constant for two-point laws

A standardized two-point law is a probability measure $\mu$ on $\mathbb{R}$ with mean $0$, variance
$1$ and finite third absolute moment (automatic here) that is concentrated on two distinct points:
$\mu(\mathbb{R} \setminus \{a, b\}) = 0$ for some reals $a \ne b$. The Berry–Esseen constant for
two-point laws, $C_B$, is the infimum of all real $C$ such that for every standardized two-point law
$\mu$ and every positive integer $n$,

$$\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le \frac{C \rho(\mu)}{\sqrt{n}},$$

where $F_n$ is the distribution function of $(X_0 + \dots + X_{n-1})/\sqrt{n}$ for independent random
variables $X_0, \dots, X_{n-1}$ with law $\mu$, $\rho(\mu) = \int |x|^3 \, d\mu(x)$, and $\Phi$ is the
standard normal distribution function.

## Idea

Two-point laws, the standardized Bernoulli laws, are natural candidates for the worst case of the
Berry–Esseen inequality: their sums are lattice valued, so their distribution functions jump, and a
jump of size $h$ forces a distance at least $h/2$ from the continuous function $\Phi$. Restricting the
inequality to them can only lower the best constant, so $C_B$ is at most the general constant $C_0$;
and $C_B \ge 0$, since admissible constants exist ($42$ works) and are nonnegative. Esseen's
asymptotic example gives $C_B \ge (\sqrt{10} + 3)/(6\sqrt{2\pi}) \approx 0.4097$, and Schulz showed in
2016 that $C_B$ equals this number. Whether the general constant $C_0$, known to lie
between this value and $0.4748$, also equals it is not known.

## Statements

- [Bernoulli Berry–Esseen constant](bernoulli-value.md)
- [Standardized two-point law](is-bernoulli-law.md): definition used in the main definition
- [Admissible Berry–Esseen coefficient for two-point laws](is-bernoulli-admissible.md): definition used in the main definition
- [Bernoulli-admissible coefficients are nonnegative](is-bernoulli-admissible-nonnegative.md): basic property of two-point admissibility
- [Bernoulli-admissible coefficients exist](bernoulli-admissible-nonempty.md): lemma: the infimum is over a nonempty set
- [The Bernoulli-admissible coefficients are bounded below](bernoulli-admissible-bdd-below.md): lemma: the infimum is over a set bounded below
- [The Bernoulli Berry–Esseen constant is nonnegative](bernoulli-value-nonnegative.md): basic property of the constant
- [The Bernoulli Berry–Esseen constant is at most the general one](bernoulli-value-le-value.md): comparison with the general constant

## Background

- [The optimal Berry–Esseen constant](../optimal-constant/README.md): the general constant, of which
  this is the two-point restriction.
