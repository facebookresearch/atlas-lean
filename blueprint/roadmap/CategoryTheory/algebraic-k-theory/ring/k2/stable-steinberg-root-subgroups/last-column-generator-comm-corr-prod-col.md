# Last Column Generator comm corr Prod Col

Last-column generator `x i n a` commutes with `corrProdCol i' a' Rl` when `i < n`,
`i' < n`, and every `q ∈ Rl` satisfies `q.1.val ≠ i`.
Orientation: `x (R := R) i n (Nat.ne_of_lt hi) a * corrProdCol (R := R) i' a' Rl =
corrProdCol (R := R) i' a' Rl * x (R := R) i n (Nat.ne_of_lt hi) a`.
Hypotheses `hi : i < n`, `hi' : i' < n`, and `hDisj : ∀ q ∈ Rl, q.1.val ≠ i` are
required. This is a commutation equality only—not normality, membership, collection,
landing, kernel, or Matsumoto. Generic over `[Ring R]` and characteristic-two safe.
