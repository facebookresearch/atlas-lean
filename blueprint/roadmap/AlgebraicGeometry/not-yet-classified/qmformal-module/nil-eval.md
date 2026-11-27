# Nil Eval

Evaluation of a power series `φ` at a point `a`, after truncating `φ`
to the monomials whose exponent in each variable is at most `n`
(`MvPowerSeries.trunc'` at the constant bound `n`), not to the monomials
of total degree at most `n`. The point `a` is arbitrary. When every `a i`
lies in an ideal `J` with `J ^ (n + 1) = ⊥`, every monomial of total
degree above `n` vanishes at `a`, so the two truncations give the same
value.
