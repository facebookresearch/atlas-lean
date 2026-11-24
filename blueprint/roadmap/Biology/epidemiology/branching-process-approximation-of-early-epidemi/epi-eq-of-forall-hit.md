# Epidemic and branching process agree while every contact hits

For offspring numbers `ξ_n(i) ∈ ℕ` (the contacts of the `i`-th infective of generation `n`), contact
targets `U_0, U_1, …` in a type `α` of individuals (contact number `j` goes to `U_j`) and a finite
set `S₀ ⊆ α` of initially susceptible individuals, and natural numbers `M` and `n`, suppose that
each of the first `M` contacts (numbers `j < M`) [hits](epi-hit.md) and that the branching process
makes at most `M` contacts in its first `n` generations, `D_n ≤ M` with `D_n` the
[contact count](bp-contacts.md). Then the [state](epi.md) of the epidemic at generation `n` is
`(Z_n, D_n)`, with `Z_n` the [generation size](bp-size.md): the epidemic and the branching process
have the same generation size and the same number of earlier contacts.
