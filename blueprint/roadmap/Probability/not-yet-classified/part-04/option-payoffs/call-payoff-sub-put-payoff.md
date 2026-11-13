# Call Payoff sub put Payoff

Call payoff minus put payoff equals terminal underlying minus strike:
`(S - K)⁺ - (K - S)⁺ = S - K`. This is `posPart_sub_negPart` once
`max (K - S) 0` is rewritten as the negative part of `S - K`; do not reprove
the Mathlib lemma.
