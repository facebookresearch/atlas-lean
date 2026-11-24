# Averaging over samples of distinct children

Let `W` be a [Cannings model](../cannings-models/cannings-model.md) of population size `N`, whose
law is exchangeable in the children, with parent map `f : {0, …, N - 1} → {0, …, N - 1}` and
expectation `E` under its law. Let `g : {0, …, m - 1} → {0, …, N - 1}` be injective (a sample of `m`
distinct children) and let `F` be any real function of a tuple of `m` parents. Then

`(N)_m E[F(f ∘ g)] = E[∑_{g'} F(f ∘ g')]`,

where the sum runs over all injective `g' : {0, …, m - 1} → {0, …, N - 1}` and
`(N)_m = N (N - 1) ⋯ (N - m + 1)` is their number. By exchangeability in the children, the parents
`f ∘ g'` of every sample of `m` distinct children have the same law.
