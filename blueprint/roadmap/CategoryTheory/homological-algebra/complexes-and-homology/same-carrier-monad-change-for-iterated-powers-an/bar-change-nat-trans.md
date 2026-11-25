# Bar Change Nat Trans

Fixed-monad-hom natural transformation packaging `barChangeHom`.

For fixed `h : T ⟶ S`, the family `barChangeHom h R L` is natural in `(R, L)`
via Mathlib's `Functor.prod` restriction. Both module variables are covariant.
Same carrier only; no carrier-change, outer-whiskering, evaluation,
balanced-tensor, or operadic API.
