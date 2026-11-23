# The Kimura distance splits into transition and transversion parts

For all real `P` and `Q`, the [Kimura distance](kimura-distance.md)
`d(P, Q) = -(1/2) · log (1 - 2P - Q) - (1/4) · log (1 - 2Q)` is the sum of the
[transition parameter](kimura-transition-param.md)
`a(P, Q) = -(1/2) · log (1 - 2P - Q) + (1/4) · log (1 - 2Q)` and twice the
[transversion parameter](kimura-transversion-param.md) `b(Q) = -(1/4) · log (1 - 2Q)`:
`d(P, Q) = a(P, Q) + 2 b(Q)`, one transition and two transversion classes.
