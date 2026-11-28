# ERM learner

A learner `A` on samples of size `m ≥ 1` follows the empirical risk
minimization rule for the loss `L` over the class `C` if, on every labelled sample `S`, its output
`A S` is an empirical risk minimizer over `C` (the rule `ERM_H` of Shalev-Shwartz and Ben-David,
*Understanding Machine Learning*, 2014, Section 2.3, with the general-loss empirical risk of
equation (3.4)). No ERM learner exists over a class on which some sample has no minimizer; when
`X` and `Y` are nonempty, that includes the empty class. When `X` or `Y` is empty there is no
labelled sample, so every learner is vacuously an ERM learner.
