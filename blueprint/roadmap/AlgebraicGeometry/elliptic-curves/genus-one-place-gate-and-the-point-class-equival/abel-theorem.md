# Abel's criterion, as a hypothesis

A divisor of degree zero is principal exactly when
`divisorSum` sends it to `0`, that is, when the points that the chosen bijection attaches to its
places sum to zero with multiplicities. For an elliptic curve with the centred bijection
(`GenusOnePlaceGate.IsCentred`) this is Abel's theorem in genus one (Silverman, *The Arithmetic of
Elliptic Curves*, Corollary III.3.5); relative to another bijection it is a separate assumption.
Equivalently, `divisorSum` descends to `Pic0` and the induced map `pic0ToPoint` is injective.
