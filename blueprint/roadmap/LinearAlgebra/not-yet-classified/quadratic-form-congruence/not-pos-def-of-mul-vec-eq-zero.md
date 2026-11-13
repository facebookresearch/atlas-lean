# Not pos Def of mul Vec eq zero

Degeneracy rules out positive definiteness: a nonzero `v` with `A *ᵥ v = 0` has
`quadForm A v = 0`, whereas `Matrix.PosDef.dotProduct_mulVec_pos` would make it positive.
