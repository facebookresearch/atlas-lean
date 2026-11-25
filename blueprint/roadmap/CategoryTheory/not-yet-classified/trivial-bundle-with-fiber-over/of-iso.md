# Of Iso

Iso transport between competing pullback presentations.

Given `h` over `f : B' ⟶ B` and a second pullback presentation `sq2` of `p`
along the same `f`, plus an isomorphism `e` of total objects with
`e.hom ≫ h.p' = q`, this returns the second presentation over the same `f`,
preserving the explicit square `sq2`. The new trivialization is
`TrivialBundleWithFiber.ofIso e heq h.trivial`; the fiber `F` is unchanged.
