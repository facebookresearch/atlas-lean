# Bar Tuple zero face

Bar-side zero-face tuple formula.

`barTuple` of the zeroth face drops the head: unfold the face to the
iterated right action, read both sides through the generalized reader,
and apply `genZeroFst`. No induction here; the induction lives once in
`genZeroSnd`/`genZeroFst` for general `X`.
