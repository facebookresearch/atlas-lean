# Variance absolute relative errors

Variances of the absolute and relative errors in the crossed
person-by-item moment model.

Persons and items are finite and nonempty; `m = Fintype.card Item`
is the common number of items per person, with `(m : ℝ) > 0`.
The score decomposition, centered square-integrable effects, the
three covariance kernels, all zero cross-block covariances (in both
orders), nonnegative variance components, and the positive item-count
denominator are all hypotheses.  The conclusions are

`Var[Delta_p grandMean X P p; μ] = (sigmaI2 + sigmae2) / m` and
  `Var[delta_p grandMean X P I p; μ] = sigmae2 / m`.
