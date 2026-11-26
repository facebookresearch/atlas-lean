# Strain-gauge calibration and its covariance

A strain gauge with gain $g \ne 0$ and offset $b$ reports the voltage $V = g\,\varepsilon + b$ for
the strain $\varepsilon$, and its calibration reads the strain back as $\varepsilon = (V - b)/g$.
These pages give the units of this calibration, its form for several gauges and the identifiability
of the strains, the weighted mean and covariance of the strains over a finite set of scenarios (the
mean and covariance of a probability distribution when the weights are nonnegative and sum to one),
their covariance under a probability mass function, and a quadratic calibration
$f(v) = c_0 + c_1 v + c_2 v^2$ with its exact Taylor remainder and the split of its output variance.

## Units of the calibration

- [Electric-potential dimension over the seven ISQ base quantities](voltage-dim.md)
- [Strain read from an affine gauge calibration with nonzero gain](gauge-strain.md)
- [Strain as a dimensionless quantity from voltage quantities](gauge-strain-qty.md)
- [Exponents of the voltage dimension at the seven ISQ base quantities](voltage-dim-exponent.md)
- [Gauge strain is unchanged by a change of units](gauge-strain-coord-dim-scale.md)
- [The coordinate of the strain quantity is the real strain formula](gauge-strain-qty-val.md)

## The calibration map and identifiability

- [Strain vector of n gauges with nonzero gains](gauge-strain-vec.md)
- [The strain vector is an affine function of the voltage vector](gauge-strain-vec-eq-affine.md)
- [Gain times strain plus offset gives back the voltage](gauge-voltage-gauge-strain.md)
- [The calibration recovers the strain from its voltage](gauge-strain-gauge-voltage.md)
- [Strains are identifiable from gain-scaled readings iff no gain is zero](identifiable-diagonal-iff.md)

## Weighted mean and covariance over finite scenarios

- [For weights summing to one, mean strain equals strain of mean voltage](mean-vec-gauge-strain-vec.md)
- [Strain covariance from voltage covariance, for weights summing to one](cov-matrix-gauge-strain-vec.md)
- [Entrywise strain covariance, for weights summing to one](cov-matrix-gauge-strain-vec-apply.md)
- [Variance of a combination of two gauge strains, cross term included](cov-matrix-two-gauges.md)
- [Nonnegative weights give nonnegative strain variances](cov-matrix-gauge-strain-vec-self-nonneg.md)

## Covariance under a probability mass function

- [Real masses of a probability mass function form a finite distribution](to-real-weights-is-distribution.md)
- [Covariance of two strain channels under a probability mass function](covariance-gauge-strain-to-measure.md)

## Quadratic calibration and its exact remainder

- [Quadratic calibration of a voltage](quad-calibration.md)
- [First-order Taylor part of the quadratic calibration](quad-linear-part.md)
- [Taylor remainder of the quadratic calibration about a base voltage](quad-remainder.md)
- [The quadratic calibration has derivative c1 + 2 c2 v at every v](quad-calibration-has-deriv-at.md)
- [Exact first-order Taylor expansion of the quadratic calibration](quad-calibration-eq-linear-add-remainder.md)
- [Quadratic calibration on dimensioned quantities](quad-calibration-qty.md)
- [Coordinate of the dimensioned quadratic calibration](quad-calibration-qty-val.md)
- [Change of units scales the quadratic calibration by the output factor](quad-calibration-coord-dim-scale.md)

## The Hessian bound, a pointwise bound only

- [Quadratic calibration as a map on one-component vectors](quad-calibration-vec.md)
- [Calibration Hessian norm is at most twice the absolute value of c2](quad-calibration-vec-hessian-le.md)
- [First-order remainder of the vector calibration is exactly c2 δ²](quad-calibration-vec-jacobian-remainder.md)
- [Pointwise remainder bound for the quadratic calibration on an interval](quad-calibration-vec-remainder-le.md)
- [For nonzero c2 the quadratic calibration is not Lipschitz on the line](quad-calibration-not-lipschitz-with.md)

## Output variance under a finite scenario law

- [Finite scenario law with every voltage in an interval](scenario-law-in.md)
- [Output variance splits into linear, remainder and cross terms](variance-quad-calibration-expansion.md)
- [Variance of the first-order part, for weights summing to one](variance-quad-linear-part.md)
- [Cross covariance of the first-order part and the remainder](covariance-quad-linear-part-quad-remaind.md)
- [Output variance of the quadratic calibration under a scenario law](variance-quad-calibration-of-scenario-la.md)
- [Output variance split under a probability mass function](variance-quad-calibration-to-measure.md)
