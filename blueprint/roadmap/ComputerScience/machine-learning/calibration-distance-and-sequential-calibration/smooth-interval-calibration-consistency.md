# Smooth and interval calibration errors are consistent and quadratically optimal

For every distribution $\Gamma$ over $[0,1] \times \{0,1\}$:

$$
\tfrac12\,\underline{\mathrm{dCE}}(\Gamma) \le \mathrm{smCE}(\Gamma) \le 2\,\underline{\mathrm{dCE}}(\Gamma), \qquad \underline{\mathrm{dCE}}(\Gamma) \le \mathrm{intCE}(\Gamma) \le 4\sqrt{\underline{\mathrm{dCE}}(\Gamma)},
$$

and $\underline{\mathrm{dCE}}(\Gamma) \le \overline{\mathrm{dCE}}(\Gamma) \le 4\sqrt{\underline{\mathrm{dCE}}(\Gamma)}$. Moreover any consistent calibration measure computable in the prediction-only access model loses at least a square: there are $(D_1, f)$ and $(D_2, f)$ inducing the same law of $(f(x), y)$ with $\mathrm{dCE}_{D_1}(f) \le 2\alpha^2$ and $\mathrm{dCE}_{D_2}(f) \ge \alpha$, so the quadratic approximations above are information-theoretically optimal. The smooth calibration error of an empirical distribution on $n$ points is computable in time polynomial in $n$ by linear programming, and the Laplace-kernel calibration error is also consistent.

## Proof sketch

The smooth calibration error is the value of a linear program whose dual is a transportation problem moving the predictions to a calibrated coupling, which is the lower distance up to a factor two (Lipschitz duality). Interval calibration upper bounds the lower distance by constructing a calibrated predictor that is constant on each interval, and the square-root upper bound comes from choosing interval widths of order $\sqrt{\underline{\mathrm{dCE}}}$. The lower-bound construction uses four-point domains on which the same prediction-outcome law arises from a nearly calibrated predictor and from one far from calibration.

## Depends on

- [Smooth calibration error and interval calibration error](smooth-calibration-error.md)
- [Distance to calibration and its upper and lower variants](distance-to-calibration.md)

## Sources

- J. Blasiok, P. Gopalan, L. Hu, P. Nakkiran, "A Unifying Theory of Distance from Calibration", STOC (2023), arXiv:2211.16886.
