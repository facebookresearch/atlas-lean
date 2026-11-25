# Genus-one place gate

A hypothesis on an affine Weierstrass curve `W` over `F`: a bijection
`pointEquivPlace` from the points of `W` to the places of its function field over `F`, and the
condition `deg_eq_one` that every place has degree one. The bijection is data, and nothing in the
class ties it to the geometry of `W`; `GenusOnePlaceGate.IsCentred` is the condition that does. The
intended instance is an elliptic curve over an algebraically closed field `F`, with each point sent
to the place centred at it. When `F` is algebraically closed and `IsCurveOver F W.FunctionField`
holds, `deg_eq_one` follows from `AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed`.
