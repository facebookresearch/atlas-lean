# Schulz's Bernoulli Berry–Esseen optimum

Let $C_B$ be the infimum of all real $C$ such that for every real probability law $\mu$ with mean $0$,
variance $1$ and finite third absolute moment $\rho = \int |x|^3 \, d\mu$ that is concentrated on two
points ($\mu(\mathbb{R} \setminus \{a, b\}) = 0$ for some reals $a \ne b$), and every integer $n \ge 1$,
the distribution function $F_n$ of $(X_1 + \dots + X_n)/\sqrt{n}$, for independent $X_1, \dots, X_n$ with
law $\mu$, satisfies $\sup_x |F_n(x) - \Phi(x)| \le C \rho / \sqrt{n}$, where $\Phi$ is the standard
normal distribution function. Then $C_B = (\sqrt{10} + 3)/(6\sqrt{2\pi}) \approx 0.4097$.

## Idea

Esseen found a two-point law whose normalized sums stay at distance about $C_E \rho/\sqrt{n}$ from the
normal law along a subsequence of $n$, where $C_E = (\sqrt{10} + 3)/(6\sqrt{2\pi})$, so no constant below
$C_E$ works for all two-point laws. Schulz proved in 2016 that $C_E$ itself works for every two-point
law and every $n$. So the worst two-point case is known exactly, while for general laws the optimal
constant is only known to lie between $C_E$ and $0.4748$.

## Statements

- [Schulz's Bernoulli Berry–Esseen optimum](schulz2016-bernoulli-optimum-holds.md)
- [Statement of Schulz's Bernoulli Berry–Esseen optimum](schulz2016-bernoulli-optimum.md): the statement as a proposition
- [Esseen's asymptotic lower bound for a two-point law](esseen-bernoulli-asymptotic-lower-bound-2.md): a stronger form of the lower half: one standardized two-point law has $\limsup_n \sqrt{n}\,\Delta_n(\mu)/\beta_3(\mu) \ge C_E$, so $C_B \ge C_E$ (Esseen)
- [Statement of Esseen's asymptotic lower bound for a two-point law](esseen-bernoulli-asymptotic-lower-bound.md): that lower bound as a proposition

## Background

- [Berry–Esseen constant for two-point laws](../two-point-laws/README.md): the constant $C_B$
- [Esseen's lower bound for the Berry–Esseen constant](../esseen-lower-bound/README.md): the constant $C_E$
