# Base Change

Base change of an over-presentation along a further pullback square.

Given `h` over `f : B' ⟶ B` and a pullback presentation `sq2` of `h.p'`
along `g : B'' ⟶ B'`, this returns the composite presentation over
`g ≫ f`, retaining the ambient map `p` and the explicit pasted square
`sq2.paste_horiz h.sq`. The new trivialization is the parent pullback
`h.trivial.pullback sq2`; the fiber `F` is unchanged.
