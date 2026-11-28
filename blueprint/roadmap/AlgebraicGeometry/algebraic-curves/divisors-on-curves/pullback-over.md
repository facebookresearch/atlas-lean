# Place Extension

The pullback of divisors along a finite separable extension `F' / F`, weighting each place of
`F'` by its ramification index. It sums over `Place.fiberOver`, so unlike `Divisor.pullback`,
which sums over `Place.fiber`, it does not need principal divisors on `F'`; the two agree when
both are defined.
