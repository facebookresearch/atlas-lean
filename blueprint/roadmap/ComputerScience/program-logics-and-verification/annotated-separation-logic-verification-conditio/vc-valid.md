# Vc valid

For an annotated command `C` and heap assertions `P`, `Q`, if
`C.vc Q` holds and `P.Entails (C.pre Q)`, then `SepValid P C.strip Q`.
Thus the erased program avoids faults from `P` and satisfies `Q` at every
terminating output; termination itself is not asserted.
