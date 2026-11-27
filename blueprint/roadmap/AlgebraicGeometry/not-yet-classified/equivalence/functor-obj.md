# Functor obj

The forward functor of `commHopfAlgCatOpEquivAffineGroupSchemeCat` sends a Hopf algebra to the
bundled Hopf spectrum, as an equality of objects. Unlike `functorObjIso`, this equality lets one
transport an arbitrary object property, with no isomorphism invariance needed, so it can be used to
rewrite `P ((commHopfAlgCatOpEquivAffineGroupSchemeCat _).functor.obj H)`.
