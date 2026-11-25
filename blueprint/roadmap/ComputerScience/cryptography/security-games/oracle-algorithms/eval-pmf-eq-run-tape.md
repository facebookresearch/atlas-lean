# Eager sampling for a single-phase algorithm

Let the randomness space `Rnd` be finite and nonempty. For an oracle algorithm
`c` making at most `q` queries, running it against the randomized oracle `m ↦
e m r` with fresh uniform `r` per query gives the same output distribution as
drawing a uniform tape `ρ : Fin q → Rnd` up front and running it against `e`
with the randomness of the `i`-th query taken from `ρ i`.
