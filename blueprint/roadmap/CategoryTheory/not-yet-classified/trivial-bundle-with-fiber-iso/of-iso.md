# Of Iso

Transport a fixed-fiber presentation across an over-base isomorphism.

Given `e : E ≅ E'` with `e.hom ≫ p' = p` and a presentation `h'` of `p'`
with fixed fiber `F`, this builds a presentation of `p` with the same fiber
and second projection `e.hom ≫ h'.r`. The proof uses the existing
product-cone limit structure with explicit isomorphism composition; inverse
equations are handled by `Category.assoc`. Only the fixed fiber is preserved;
no chart beyond the two presentations is claimed.
