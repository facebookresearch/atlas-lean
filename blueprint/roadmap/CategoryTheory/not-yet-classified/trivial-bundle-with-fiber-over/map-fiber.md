# Map Fiber

Fiber-side transport of an over-presentation along a fiber isomorphism.

Given `e : F ≅ G` and `h` over `f` with fixed fiber `G`, this returns the same
pullback presentation (`h.E'`, `h.p'`, `h.t`, `h.sq`) with fixed fiber `F` via
`h.trivial.mapFiber e`. Only the supplied fiber iso changes the fiber; the base
map, ambient map, and explicit square are unchanged. No gluing, descent, chart,
or model claim is made.
