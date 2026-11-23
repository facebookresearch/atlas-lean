# Sum expected SFS neutral

Expected total number of segregating sites (Watterson's formula, with the
sum explicit): in the neutral infinite-sites model, the sum of
`expectedSFS θ 0 n i` over the segregating classes `1 ≤ i < n` equals `θ`
times the harmonic sum over those classes. The monomorphic class `i = n` is
excluded, matching `expectedSFS_neutral`. The class `i = 0` is also excluded:
there the integrand is not integrable and the model has an infinite expected
number of ancestral-monomorphic sites; separately, Lean assigns its arbitrary
junk value `0` to a non-integrable real integral, so that Lean value is not an
expectation result.
