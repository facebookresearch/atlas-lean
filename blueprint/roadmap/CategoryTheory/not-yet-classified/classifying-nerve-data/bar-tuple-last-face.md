# Bar Tuple last face

Bar-side last-face tuple formula.

`barTuple` of the last face drops the tail: unfold the face to the left
point action (`barFaceApp_of_val_last`), read both sides through the
generalized reader, and apply `genLastFst`. No induction here; the induction
lives once in `genMapSnd`/`genMapFst`.
