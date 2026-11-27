# Sum neg one pow smul sum neg one pow smul eq zero

An alternating double sum `∑ i, (-1)ⁱ • ∑ j, (-1)ʲ • F i j` vanishes when its terms satisfy
the simplicial identity `F (j + 1) i = F i j` for `i ≤ j`: the terms with `i ≤ j` cancel against
those with `j < i`. With `F i j = φ (d_j (d_i x))` this is `d ∘ d = 0` for an alternating sum of
faces `dᵢ`; the argument is that of Mathlib's
`AlgebraicTopology.AlternatingFaceMapComplex.d_squared`.
