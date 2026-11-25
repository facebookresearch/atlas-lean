# State of the epidemic at generation n

For offspring numbers `ξ_n(i) ∈ ℕ` (the contacts of the `i`-th infective of generation `n`), contact
targets `U_0, U_1, …` in a type `α` of individuals (contact number `j` goes to `U_j`) and a finite
set `S₀ ⊆ α` of initially susceptible individuals, the state `(I_n, D_n)` of the epidemic at
generation `n` (the number of infectives of generation `n` and the number of contacts made by the
earlier generations) is defined by `(I_0, D_0) = (1, 0)` and

`I_{n+1} = #{j : D_n ≤ j < D_n + c_n, contact j hits}`, `D_{n+1} = D_n + c_n`,

where `c_n = ∑_{i < I_n} ξ_n(i)` is the number of contacts made by generation `n`. Generation `0` is
the index case alone, with no earlier contacts; generation `n` makes the contacts numbered
`D_n, …, D_n + c_n − 1`, and the next generation consists of the targets of those that
[hit](epi-hit.md).
