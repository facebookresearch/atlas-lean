# Uniform deviation for a finite class

Let $\mathcal{F}$ be a finite nonempty set of predictors, let $\ell$ be a loss with values in
$[0, \ell_\infty]$ for some $\ell_\infty > 0$ such that for each $f \in \mathcal{F}$ the map
$z = (x, y) \mapsto \ell(y, f(x))$ is measurable, and let $z_1 = (x_1, y_1), \dots,
z_n = (x_n, y_n)$, with $n \ge 1$, be independent and identically distributed examples. For
$f \in \mathcal{F}$ write $R(f) = \mathbb{E}\,\ell(y, f(x))$ for the expected risk and
$\hat R(f) = \frac{1}{n}\sum_{i=1}^{n} \ell(y_i, f(x_i))$ for the empirical risk. Then for every
$t > 0$,

$$
\mathbb{P}\Big(\max_{f \in \mathcal{F}} \lvert \hat R(f) - R(f) \rvert > t\Big)
\le 2\,\lvert \mathcal{F} \rvert \exp\Big(-\frac{2 n t^2}{\ell_\infty^2}\Big),
$$

and so, for every $\delta \in (0, 1]$, with probability at least $1 - \delta$,

$$
\max_{f \in \mathcal{F}} \lvert \hat R(f) - R(f) \rvert
\le \ell_\infty \sqrt{\frac{\log(2 \lvert \mathcal{F} \rvert / \delta)}{2n}}.
$$

Derivation: for a fixed $f$, the variables $\ell(y_i, f(x_i)) / \ell_\infty$ are independent, take
values in $[0, 1]$ and have mean $R(f) / \ell_\infty$, so the two-sided Hoeffding inequality bounds
the probability that $\lvert \hat R(f) - R(f) \rvert$ exceeds $t$ by
$2 \exp(-2 n t^2 / \ell_\infty^2)$. The event on the left is the union of these $\lvert \mathcal{F}
\rvert$ events, and the probability of a finite union is at most the sum of the probabilities. The
second statement takes $t = \ell_\infty \sqrt{\log(2 \lvert \mathcal{F} \rvert / \delta) / (2n)}$,
for which the right-hand side equals $\delta$, and passes to the complementary event. The maximum
over a finite class is measurable because each $\hat R(f)$ is, by the measurability of each map
$z \mapsto \ell(y, f(x))$.

A uniform bound of this kind controls empirical risk minimization (derived): if
$\hat f \in \mathcal{F}$ minimizes $\hat R$ and $s = \max_{f} \lvert \hat R(f) - R(f) \rvert$, then
for every $f \in \mathcal{F}$, $R(\hat f) \le \hat R(\hat f) + s \le \hat R(f) + s \le R(f) + 2s$.

The source states this bound for a loss with values in $[0, \ell_\infty]$ and i.i.d. examples,
with the per-predictor Hoeffding step for independent variables in $[0, 1]$; the exact forms above
(the strict event, the measurability remark and the constants) are derived here.

The same bound for every loss with values in $[0, \ell_\infty]$, with the non-strict event
$|\hat R(f) - R(f)| \ge t$, is
[Uniform deviation of the empirical risk over a finite class](measure-real-exists-abs-empirical-risk-s.md),
its high-probability form is
[Uniform deviation over a finite class, high-probability form](one-sub-le-measure-real-forall-abs-empir.md),
and the consequence for empirical risk minimization is
[Empirical risk minimization under a uniform deviation bound](risk-le-add-two-mul-of-forall-abs-sub-le.md).

## Informally uses

- [Two-sided Hoeffding inequality for averages of bounded variables](../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md):
  mathematical prerequisite, the per-predictor bound $2 \exp(-2 n t^2 / \ell_\infty^2)$ for the
  variables $\ell(y_i, f(x_i)) \in [0, \ell_\infty]$, here for the non-strict event, which contains
  the strict one.
- [Two-sided Hoeffding inequality for Bernoulli sums](../../../Probability/concentration-inequalities/hoeffding-s-inequality/hoeffding-bernoulli-sum-abs-tail.md):
  mathematical prerequisite in a restricted case, the per-predictor bound when the loss takes only
  the values $0$ and $1$ ($\ell_\infty = 1$): with $X_i = \ell(y_i, f(x_i))$ and
  $p = R(f)$ it is exactly the bound $2 \exp(-2 n t^2)$ on the event
  $\lvert \hat R(f) - R(f) \rvert > t$.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF dated 26 May 2025 at <https://www.di.ens.fr/~fbach/ltfp_book.pdf> (page numbers are those printed in that PDF; their correspondence with the MIT Press 2024 print edition was not checked), Section 4.4.3 (finite number of models), printed page 88 (the union bound and the high-probability bound), and Section 1.2.1, Proposition 1.2 and Corollary 1.1, printed pages 10–11 (Hoeffding's inequality for independent variables in $[0, 1]$).
- AI-authored exposition.
