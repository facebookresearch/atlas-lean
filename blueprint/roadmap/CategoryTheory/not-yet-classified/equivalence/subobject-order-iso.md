# Subobject Order Iso

The order isomorphism on subobject lattices induced by an equivalence of categories.

It is obtained by composing `MonoOver.congr` with `Subobject.lowerEquivalence` and then
`Equivalence.toOrderIso`. Using these existing equivalences avoids rebuilding subobject
transport by hand.
