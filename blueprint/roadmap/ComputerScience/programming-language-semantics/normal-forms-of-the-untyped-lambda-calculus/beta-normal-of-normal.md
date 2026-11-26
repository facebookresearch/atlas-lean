# Relational normal forms are syntactic normal forms

A locally closed term with no full
β-step contains no β-redex. Local closure is needed: `app (abs (bvar 0)) (bvar 1)` has no full
β-step but contains a redex. The conclusion is the hypothesis of `Term.Leftmost.normalization`.
