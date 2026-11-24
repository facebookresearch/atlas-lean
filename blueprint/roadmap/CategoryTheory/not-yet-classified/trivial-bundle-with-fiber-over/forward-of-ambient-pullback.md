# Forward Of Ambient Pullback

Forward ambient transport of an over-presentation along an ambient pullback.

Given `h` over `f_old : B' ⟶ B_old`, an ambient pullback `sqA` presenting
`p_new` as the pullback of `p_old` along `b`, a base compatibility
`hBase : f_new ≫ b = g ≫ f_old`, and a pullback `sq2` of `h.p'` along `g`,
this returns the composite presentation over `f_new : B'' ⟶ B_new` with the
same fiber `F`. The new trivialization is the parent pullback
`h.trivial.pullback sq2`; the new square is the left cancellation
`IsPullback.of_right'` of the pasted outer against `sqA`. No global chart,
monodromy, Serre, weak-equivalence, model, or KQ3 claim is made.
