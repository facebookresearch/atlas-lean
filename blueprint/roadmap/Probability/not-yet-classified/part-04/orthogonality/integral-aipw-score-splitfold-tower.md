# Integral aipw Score splitfold tower

Tower form: the joint bias over training and evaluation is the training
mean of the fiber product-bias sums.

Clause map: "two independent folds" is the product law `μₜ.prod μ` (independence
is the product structure); "fitted nuisances fixed given training" is that
`mhat`/`ehat` enter the evaluation score only through the training coordinate
`z.1`; "fiber identity" is the pointwise application of
`integral_aipwScore_eq` at each training outcome;
"tower form" is the conclusion, through Bochner Fubini
(`MeasureTheory.integral_prod`). "Trained only on training data" is the
restriction that the score reads the training coordinate solely through
`mhat`/`ehat`: a nuisance trained on the evaluation outcome is not a function
of the training fold alone, so same-sample fitting is not an instance of either
target. `hint` (joint integrability of the score) is the load-bearing premise:
without it Fubini does not apply, because fiberwise integrability supplies no
domination over the training law when the fitted nuisances are unbounded in the
training coordinate; it also supplies the a.e. strong measurability the Fubini
argument needs.
