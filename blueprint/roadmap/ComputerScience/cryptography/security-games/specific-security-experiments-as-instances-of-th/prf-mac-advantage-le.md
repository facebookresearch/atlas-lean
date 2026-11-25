# The PRF-MAC bound

Let the key space `K` and the forger's coin space `R` be finite and nonempty,
and let the messages `M` have decidable equality. Let `M` and `T` be finite,
`T` nonempty with decidable equality, and `F : K → M → T`. For every forger `A
: R → OracleComp M T (M × T)` with uniform coins, its forgery advantage
against `prfMac F` is at most the PRF advantage against `F` of the
distinguisher `fun r => macReduction [] (A r)`, plus `1 / |T|` (Katz and
Lindell, Theorem 4.6).
