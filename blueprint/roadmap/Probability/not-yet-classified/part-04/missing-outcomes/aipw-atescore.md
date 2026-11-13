# Aipw ATEScore

The **AIPW score for the average treatment effect** with treatment event `T`, a fixed
treatment propensity `e` and fixed arm regressions `m₀`, `m₁`: the missing-outcome score of the
treated arm (response event `T`, propensity `e`) minus that of the control arm (response event
`Tᶜ`, propensity `1 - e`). Applied to the observed outcome `observed T Y₀ Y₁`.

It equals, pointwise, the AIPW ATE score of `AugmentedIPW/Score.lean` (task T28, not merged at
the time of writing), `aipwScore T X Y e m₀ m₁` there, up to argument order; the two are to be
unified at integration.
