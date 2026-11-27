# Smooth and interval calibration errors are consistent and quadratically optimal

For every distribution $\Gamma$ over $[0,1] \times \{0,1\}$:

$$
\tfrac12\,\underline{\mathrm{dCE}}(\Gamma) \le \mathrm{smCE}(\Gamma) \le 2\,\underline{\mathrm{dCE}}(\Gamma), \qquad \underline{\mathrm{dCE}}(\Gamma) \le \overline{\mathrm{dCE}}(\Gamma) \le \mathrm{intCE}(\Gamma) \le 4\sqrt{\underline{\mathrm{dCE}}(\Gamma)} .
$$

Consequently, for every $(D,f)$ the smooth calibration error is $(1,2)$-consistent and the interval calibration error is $(\tfrac12,1)$-consistent: $\mathrm{dCE}_D(f) \le \mathrm{intCE}_D(f) \le 4\sqrt{\mathrm{dCE}_D(f)}$ and $\tfrac{1}{32}\mathrm{dCE}_D(f)^2 \le \mathrm{smCE}_D(f) \le 2\,\mathrm{dCE}_D(f)$. Moreover the square cannot be avoided: for every $\alpha \in (0, \tfrac12]$ there are $(D_1, f)$ and $(D_2, f)$ inducing the same law of $(f(x), y)$ with $\mathrm{dCE}_{D_1}(f) \le 2\alpha^2$ and $\mathrm{dCE}_{D_2}(f) \ge \alpha$, so every $(c,s)$-consistent measure computable in the prediction-only access model has $s \ge 2c$. The smooth calibration error of an empirical distribution on $n$ points is computable in time polynomial in $n$ by linear programming. The kernel calibration error for the Laplace kernel $K(u,v) = e^{-|u-v|}$, the supremum of $\mathbb{E}_\Gamma[h(v)(y - v)]$ over the unit ball of its reproducing kernel Hilbert space, satisfies $c_1\,\underline{\mathrm{dCE}}(\Gamma) \le \mathrm{kCE}_{\mathrm{Lap}}(\Gamma) \le c_2 \sqrt{\underline{\mathrm{dCE}}(\Gamma)}$ for absolute constants $c_1, c_2 > 0$, so it is consistent as well.

## Proof sketch

The smooth calibration error is the value of a linear program whose dual is a transportation problem moving the predictions to a calibrated coupling, which is the lower distance up to a factor two (Lipschitz duality). Interval calibration upper bounds the upper distance: mapping each $v$ in an interval $I$ to $\mathbb{E}[y \mid v \in I]$ is a calibrated post-processing whose distance from $v$ is at most the binned error plus the average width. For the square-root upper bound, a randomly shifted partition into intervals of width $\varepsilon$ separates the two coordinates of an optimal coupling with probability at most $|u-v|/\varepsilon$, so its binned error is at most $(1+2/\varepsilon)\,\underline{\mathrm{dCE}}$; adding the width $\varepsilon$ and optimizing over $\varepsilon$ gives $4\sqrt{\underline{\mathrm{dCE}}}$. The consequences for $\mathrm{dCE}_D(f)$ use $\underline{\mathrm{dCE}} \le \mathrm{dCE}_D(f) \le \overline{\mathrm{dCE}}$. The lower-bound construction uses four-point domains on which the same prediction-outcome law arises from a nearly calibrated predictor and from one far from calibration.

## Depends on

- [Smooth calibration error and interval calibration error](smooth-calibration-error.md)
- [Distance to calibration and its upper and lower variants](distance-to-calibration.md)

## Sources

- J. Blasiok, P. Gopalan, L. Hu, P. Nakkiran, "A Unifying Theory of Distance from Calibration", STOC (2023), arXiv:2211.16886, Lemma 4.5, Corollaries 4.6 and 6.4, Theorems 6.2, 7.3, 7.14 and 8.5.
