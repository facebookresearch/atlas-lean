# Shevtsova's upper bound for the Berry–Esseen constant

Let $C_0$ be the optimal Berry–Esseen constant for identically distributed summands, the infimum of all real $C$ such that for every probability measure $\mu$ on $\mathbb{R}$ with
mean $0$, variance $1$ and finite third absolute moment $\rho = \int |x|^3 \, d\mu$, and every integer
$n \ge 1$,

$$\sup_{x \in \mathbb{R}} |F_n(x) - \Phi(x)| \le \frac{C \rho}{\sqrt{n}},$$

where $F_n$ is the distribution function of $(X_1 + \dots + X_n)/\sqrt{n}$ for independent random
variables $X_1, \dots, X_n$ with law $\mu$, and $\Phi$ is the standard normal distribution function.
Shevtsova's 2011 bound states that $C_0 \le 0.4748$.

## Idea

Every proof of the Berry–Esseen theorem yields an explicit constant, and sharpening it has a long
history, which the statements of this card trace: $0.82$ (Zolotarev, 1967), $0.7975$ (van Beek, 1972),
$0.7655$ (Shiganov, 1986), $0.7056$ (Shevtsova, 2006), $0.5129$ (Korolev and Shevtsova, 2009),
$0.4785$ (Tyurin, 2009) and $0.4748$ (Shevtsova, 2011). The card also records three smaller values that
are not treated here as established: $0.4690$, attributed to Shevtsova (2013), whose derivation has not
been checked against its primary source, and two claims from 2026, $0.4395$ (Xiao and Li) and $0.423$
(Lin), which are unverified. The methods refine the
characteristic-function proof: sharper smoothing inequalities, careful estimates of the characteristic
function of the sum, and extensive numerical computation for small $n$. A structural variant bounds the
error by $0.34445\,(\rho + 0.489)/\sqrt{n}$, which is better than $0.4748\,\rho/\sqrt{n}$ when $\rho$
is large. Esseen's lower bound, about $0.4097$, shows how little room remains.

## Statements

- [Shevtsova's 2011 Berry–Esseen bound](shevtsova2011-upper-bound-holds.md)
- [Statement of Shevtsova's 2011 Berry–Esseen bound](shevtsova2011-upper-bound.md): statement of the main bound
- [Statement of Zolotarev's Berry–Esseen bound](zolotarev1967-upper-bound.md): statement, weaker earlier bound
- [Zolotarev's upper bound for the Berry–Esseen constant](zolotarev1967-upper-bound-holds.md): weaker earlier bound
- [Statement of van Beek's Berry–Esseen bound](van-beek1972-upper-bound.md): statement, weaker earlier bound
- [Van Beek's upper bound for the Berry–Esseen constant](van-beek1972-upper-bound-holds.md): weaker earlier bound
- [Statement of Shiganov's Berry–Esseen bound](shiganov1986-upper-bound.md): statement, weaker earlier bound
- [Shiganov's upper bound for the Berry–Esseen constant](shiganov1986-upper-bound-holds.md): weaker earlier bound
- [Statement of Shevtsova's 2006 Berry–Esseen bound](shevtsova2006-upper-bound.md): statement, weaker earlier bound
- [Shevtsova's 2006 Berry–Esseen bound](shevtsova2006-upper-bound-holds.md): weaker earlier bound
- [Statement of the Korolev–Shevtsova upper bound](korolev-shevtsova2009-upper-bound.md): statement, weaker earlier bound
- [Korolev–Shevtsova upper bound for the Berry–Esseen constant](korolev-shevtsova2009-upper-bound-holds.md): weaker earlier bound
- [Statement of Tyurin's Berry–Esseen bound](tyurin2009-upper-bound.md): statement, weaker earlier bound
- [Tyurin's upper bound for the Berry–Esseen constant](tyurin2009-upper-bound-holds.md): weaker earlier bound
- [Statement of Shevtsova's 2013 Berry–Esseen bound](shevtsova2013-upper-bound.md): statement of a smaller later bound, not checked against its primary source
- [Shevtsova's 2013 Berry–Esseen bound](shevtsova2013-upper-bound-holds.md): smaller later bound (0.4690), not checked against its primary source
- [Statement of the unverified Berry–Esseen bound 0.4395](xiao-li2026-unverified-upper-bound.md): statement, stronger unverified claim
- [The unverified upper bound 0.4395 for the Berry–Esseen constant](xiao-li2026-unverified-upper-bound-holds.md): stronger unverified claim (0.4395)
- [Statement of Lin's 2026 Berry–Esseen bound](lin2026-unverified-upper-bound.md): statement, stronger unverified claim
- [Lin's 2026 Berry–Esseen bound](lin2026-unverified-upper-bound-holds.md): stronger unverified claim (0.423)
- [Statement of the Korolev–Shevtsova structural Berry–Esseen bound](korolev-shevtsova2009-structural.md): statement of a structural improvement
- [Korolev–Shevtsova structural Berry–Esseen bound](korolev-shevtsova2009-structural-holds.md): structural form, better than the main bound when $\rho$ is large

## Background

- [The optimal Berry–Esseen constant](../optimal-constant/README.md): the constant $C_0$ bounded here.

## Sources

- I. G. Shevtsova, "On the absolute constants in the Berry–Esseen type inequalities for identically
  distributed summands", 2011.
