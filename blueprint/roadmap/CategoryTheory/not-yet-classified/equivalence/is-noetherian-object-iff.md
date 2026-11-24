# Is Noetherian Object iff

An equivalence of categories preserves and reflects the property of being a
Noetherian object.

The proof transports the monotone chain condition
`isNoetherianObject_iff_monotone_chain_condition` along the order isomorphism
`subobjectOrderIso e X`, which itself is built from `MonoOver.congr`,
`Subobject.lowerEquivalence`, and `Equivalence.toOrderIso`.
