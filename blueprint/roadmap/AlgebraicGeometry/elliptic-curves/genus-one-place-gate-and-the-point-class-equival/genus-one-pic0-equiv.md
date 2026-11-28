# Genus-one `Pic0` as the group of points, under the two hypotheses

The additive isomorphism
`Pic0 F W.FunctionField ≃+ W.Point` induced by `GenusOnePlaceGate W` and `AbelTheorem W`: it sends
the class of a divisor `D` of degree zero to `divisorSum D`, and its inverse is `pointClass`
(`genusOnePic0Equiv_symm_apply`). It depends on the chosen bijection `pointEquivPlace`. For an
elliptic curve over an algebraically closed field with the centred bijection
(`GenusOnePlaceGate.IsCentred`), it is the isomorphism of Silverman, *The Arithmetic of Elliptic
Curves*, Proposition III.3.4.
