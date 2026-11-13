# Is Valid PValue fisher Randomization

Fisher randomization test: the full symmetric-group permutation p-value of
any measurable treatment-set statistic is valid under complete randomization.
Clause map: fixed potential outcomes with no interference enter through the
arbitrary statistic `T` of the treated set and its measurability `hT`; the
sharp null is the use case `T = diffInMeans y₀ y₀` (see the test file);
relabeling invariance of the assignment law is
`invariant_completeRandomization_map_image`; validity is the `IsValidPValue`
conclusion, via `isValidPValue_permutationPValue`; the assignment law is
normalized by `h`, discharged through
`isProbabilityMeasure_completeRandomization`.
