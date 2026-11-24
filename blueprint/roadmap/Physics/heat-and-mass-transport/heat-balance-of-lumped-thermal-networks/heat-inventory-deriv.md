# Heat inventory deriv

Zone heat inventory balance: for zones indexed by a fintype,
with constant capacities `C i`, reciprocal conductances
`G i j = G j i`, zone temperatures `T i t` with supplied derivatives
`Tv i t`, and zone equations
`C i * Tv i t = Σ j, G i j * (T j t - T i t) + b i t + P i t`,
the total heat inventory `Σ i, C i * T i t` has derivative
`Σ i, (b i t + P i t)`: internal exchange cancels by reciprocity.
