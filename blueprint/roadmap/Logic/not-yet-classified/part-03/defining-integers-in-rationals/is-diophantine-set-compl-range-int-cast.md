# Koenigsmann: `ℚ ∖ ℤ` is a Diophantine subset of `ℚ`

The set of rational numbers that are
not integers is Diophantine over `ℚ` with integer coefficients
(`MetaMathlibExt.IsDiophantineSet (Int.castRingHom ℚ)`): there are `n ∈ ℕ` and finitely many
polynomials with integer coefficients in the variables `t, y₁, …, yₙ` such that a rational `t` is
not an integer if and only if they have a common zero `(t, y₁, …, yₙ)` with `y ∈ ℚⁿ`.

This is J. Koenigsmann, "Defining ℤ in ℚ", Ann. of Math. 183 (2016), Corollary 2: "ℚ ∖ ℤ is
diophantine in ℚ". It follows from
`not_mem_range_intCast_iff_exists_eval_eq_zero_koenigsmann` by taking the one polynomial `f`.
