# Bar Tuple middle face

Bar-side middle-face tuple formula.

`barTuple` of an interior face multiplies the two adjacent entries:
unfold the face to `barMuAtPos` (`barFaceApp_of_middle`), read both sides
through the generalized reader, and apply `genMuFst`. The public
`barMuAtPos` wrapper counts from the right-module end, so `k.rev` restores
the head-first tuple position `k`. No induction here.
