# Last Column Generator comm two List Corr Col

Last-column generator `x i n a` commutes with `twoListCorrCol Rl Cs` when `i < n`
and every `q ∈ Rl` satisfies `q.1.val ≠ i`.
Orientation: `x (R := R) i n a * twoListCorrCol (R := R) Rl Cs =
twoListCorrCol (R := R) Rl Cs * x (R := R) i n a`.
Hypotheses `hi : i < n` and disjointness `hDisj` are required. This is a commutation
equality only—not normality, membership, collection, landing, kernel, or Matsumoto.
Generic over `[Ring R]` and characteristic-two safe.
