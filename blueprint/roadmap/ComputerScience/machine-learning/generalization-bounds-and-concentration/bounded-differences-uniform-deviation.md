# Concentration of the uniform deviation

Let $z_1, \dots, z_n$, with $n \ge 1$, be independent and identically distributed examples, let
$\mathcal{F}$ be a nonempty class of predictors and let the loss $\ell$ take values in
$[0, \ell_\infty]$ for some $\ell_\infty > 0$, with the map $z = (x, y) \mapsto \ell(y, f(x))$
measurable for each $f \in \mathcal{F}$. With $R$ and $\hat R$ the expected and empirical risks, consider the
uniform deviation

$$
H(z_1, \dots, z_n) = \sup_{f \in \mathcal{F}} \big(R(f) - \hat R(f)\big),
$$

and assume that $H$ is measurable, as it is when $\mathcal{F}$ is countable, since each
$R(f) - \hat R(f)$ is then measurable. Then for every
$\delta \in (0, 1]$, with probability at least $1 - \delta$,

$$
H \le \mathbb{E}[H] + \ell_\infty \sqrt{\frac{\log(1 / \delta)}{2n}}.
$$

Derivation: replacing one example $z_i$ by another changes each $\hat R(f)$ by at most
$\ell_\infty / n$, so it changes $R(f) - \hat R(f)$ by at most $\ell_\infty / n$ for every $f$,
and hence changes the supremum $H$ by at most $\ell_\infty / n$. $H$ takes values in
$[-\ell_\infty, \ell_\infty]$. McDiarmid's bounded-differences inequality with every constant
equal to $\ell_\infty / n$ gives $\mathbb{P}(H - \mathbb{E}[H] \ge t) \le
\exp(-2 n t^2 / \ell_\infty^2)$ for $t > 0$; taking
$t = \ell_\infty \sqrt{\log(1/\delta) / (2n)}$ and passing to the complementary event gives the
bound (for $\delta = 1$ it is trivial). The same argument applies to
$\sup_{f} (\hat R(f) - R(f))$, and a union bound over the two events replaces $\log(1/\delta)$ by
$\log(2/\delta)$ when both deviations are bounded at once. The source writes these bounds with
probability greater than $1 - \delta$ for $\delta \in (0, 1)$, with the loss bounded on the
support of the data; the form above, with probability at least $1 - \delta$ for
$\delta \in (0, 1]$, is derived.

This reduces a high-probability bound on the uniform deviation to a bound on its expectation, which
is controlled separately, for example by symmetrization with Rademacher complexities in the source;
this page does not cover that step. The [Rademacher complexity](rademacher-complexity/README.md)
topic develops the complexity side, and [the Rademacher risk bound](rademacher-complexity/risk-le-empirical-add-rademacher.md)
records the combined statement of Bartlett and Mendelson, with this inequality as its first step.

When the examples take finitely many values, the one-sided bound above is the finite i.i.d.
McDiarmid inequality with $c_i = \ell_\infty / n$, so that $\sum_i c_i^2 = \ell_\infty^2 / n$.
For examples in a general measurable space, the step is the classical McDiarmid inequality.

## Informally uses

- [McDiarmid's bounded-differences inequality, finite i.i.d. case](../../../Probability/concentration-inequalities/mcdiarmid-s-inequality/mcdiarmid-one-sided-finite-iid.md):
  mathematical prerequisite in a restricted case, the one-sided bound
  $\exp(-2 n t^2 / \ell_\infty^2)$ when the examples take finitely many values, with every
  sensitivity equal to $\ell_\infty / n$.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF dated 26 May 2025 at <https://www.di.ens.fr/~fbach/ltfp_book.pdf> (page numbers are those printed in that PDF; their correspondence with the MIT Press 2024 print edition was not checked), Section 4.4.1, printed pages 86–87 (McDiarmid's inequality applied to the uniform deviation, and the union bound for both deviations), Section 1.2.2, Proposition 1.3, printed page 13 (McDiarmid's inequality with a common constant), and Section 4.5.1, Proposition 4.2, printed page 92 (symmetrization).
- AI-authored exposition.
