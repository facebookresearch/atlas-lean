# PRF forgery game equals the MAC forgery experiment of the PRF-MAC

Let the key space `K` and the forger's coin space `R` be finite and nonempty,
and let the messages `M` have decidable equality. Let the tags `T` have
decidable equality, `F : K → M → T` and `A : R → OracleComp M T (M × T)`. The
PRF forgery experiment of `F` against `A` equals the MAC forgery experiment of
`prfMac F` against the forger with uniform coins built from `A` (Katz and
Lindell, Construction 4.5 and Definition 4.2).
