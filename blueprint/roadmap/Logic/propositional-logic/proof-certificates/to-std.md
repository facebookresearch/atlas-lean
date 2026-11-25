# To Std

Translate Atlas CNF to core `Std.Sat.CNF Nat`.

Atoms are unchanged Nat variables, each literal's polarity
and each clause/formula list structure are preserved via
`Std.Sat.CNF.Clause.ofLiterals`.
