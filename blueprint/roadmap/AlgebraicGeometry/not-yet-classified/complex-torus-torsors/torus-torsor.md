# Torus Torsor

`q : X ⟶ Y` is a `Gm`-torsor for the action `A` (Mathlib's `ModObj Gm X`,
passed explicitly since a scheme can carry several actions): `q` is invariant,
smooth and surjective, and `(g, x) ↦ (x, g • x)` is an isomorphism onto
`X ×_Y X`. The action of `ℂˣ` on complex points is part of the data, pinned
down by `compatibility` (it is the action induced by `A`), and is continuous.
It depends on `A`, so it is not a global instance: use `torsorBorel`, or
`letI := T.mulAction`.
