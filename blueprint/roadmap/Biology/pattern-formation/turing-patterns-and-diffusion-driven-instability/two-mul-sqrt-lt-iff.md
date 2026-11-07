# Turing condition in squared form

The Turing condition in squared form: `2 √(d_u d_v det J) < S` iff `0 < S` and
`4 d_u d_v det J < S²`, where `S = d_v f_u + d_u g_v`. This holds for all real inputs: when
`d_u d_v det J < 0`, `Real.sqrt` returns `0` and both sides reduce to `0 < S`.
