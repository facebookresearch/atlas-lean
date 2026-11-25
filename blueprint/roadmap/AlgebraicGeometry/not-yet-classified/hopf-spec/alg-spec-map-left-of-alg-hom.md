# Alg Spec map left of Alg Hom

Applying `algSpec` to an algebra homomorphism has underlying scheme map `Spec.map` of its
underlying ring homomorphism.

Mathlib's `algSpec_map_left` leaves this map expressed through the `CommAlgCat`/under-category
equivalence, and no public computation lemma exposes the resulting `Under.Hom.right`. The final
reduction is therefore definitional and is localized here.
