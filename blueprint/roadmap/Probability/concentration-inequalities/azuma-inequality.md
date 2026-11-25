# Azuma's inequality

Let $Z_0, Z_1, \dots$ be a martingale with respect to a filtration on a probability space, let $n$
be a natural number and $c_1, \dots, c_n$ real numbers, and suppose that
$|Z_i - Z_{i-1}| \le c_i$ everywhere for $1 \le i \le n$. Then for every $a > 0$,

$$\Pr[Z_n - Z_0 \ge a] \le \exp\Big(-\frac{a^2}{2 \sum_{i=1}^n c_i^2}\Big),$$

where the right side is read as $1$ if $\sum_i c_i^2 = 0$.

For $n \ge 1$, $c_i = 1$ and $a = \lambda \sqrt n$ with $\lambda > 0$, this reads $\Pr[Z_n - Z_0 \ge \lambda\sqrt n] \le e^{-\lambda^2/2}$.
For a sum of independent variables with $|X_i| \le c_i$ it is Hoeffding's inequality for the
ranges $[-c_i, c_i]$.

## Background

- [Hoeffding's inequality](hoeffding-s-inequality/README.md): the special case of independent increments.
- [McDiarmid's inequality](mcdiarmid-s-inequality/README.md): the sharp bounded-differences inequality; Azuma applied to the Doob martingale gives it only with a constant 4 times worse in the exponent.

## Sources

- Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes, Spring 2019, https://yufeizhao.com/pm/sp19/pmnotes.pdf, Theorem 8.6 and Section 8.1 (exposure martingales).
