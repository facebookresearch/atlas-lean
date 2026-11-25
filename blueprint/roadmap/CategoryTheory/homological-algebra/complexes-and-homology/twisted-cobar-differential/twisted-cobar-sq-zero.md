# Twisted Cobar sq zero

Square-zero of the left-twisted cobar differential from the Maurer–Cartan
equation: two applications of `twistedCobarDifferential τ` annihilate any
cochain. The middle terms cancel by `conv_leibniz` at degree one (the sign
`(1 : ℤ).negOnePow = -1`), and the curvature factors on the left by
`conv_assoc` and `conv_add_left` before `IsMaurerCartan` and `conv_zero_left`
close the proof. Degree transports are all `by omega` at components, so no
tensor-level descent is needed.
