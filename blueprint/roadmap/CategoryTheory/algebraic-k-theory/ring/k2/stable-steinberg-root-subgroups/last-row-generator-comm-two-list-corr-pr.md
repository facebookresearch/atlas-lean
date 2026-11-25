# Last Row Generator comm two List Corr Prod

Last-row generator `x n j b` commutes with `twoListCorrProd C Rl` when `j < n`
and every `p ∈ C` satisfies `p.1.val ≠ j`.
Orientation: `x (R := R) n j (Ne.symm (Nat.ne_of_lt hj)) b * twoListCorrProd (R := R) C Rl =
twoListCorrProd (R := R) C Rl * x (R := R) n j (Ne.symm (Nat.ne_of_lt hj)) b`.
Hypotheses `hj : j < n` and `hCj : ∀ p ∈ C, p.1.val ≠ j` are required. This is a
commutation equality only—not normality, membership, collection, landing, kernel,
or Matsumoto. Generic over `[Ring R]` and characteristic-two safe.
