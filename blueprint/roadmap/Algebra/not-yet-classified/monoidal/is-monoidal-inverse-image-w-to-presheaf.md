# Tensoring preserves morphisms inverted by sheafification

Let `𝒪` be a presheaf of
commutative rings on a site `(C, J)` on which presheaves of abelian groups have sheafifications
and `J.W` consists of the locally bijective morphisms, and let `α` be a locally injective and
locally surjective morphism from the underlying presheaf of rings of `𝒪` to a sheaf of rings `R`.
Then the morphisms of presheaves of `𝒪`-modules whose underlying morphism of presheaves of
abelian groups becomes an isomorphism after sheafification (lies in `J.W`) are stable under
tensoring, on either side, with any presheaf of `𝒪`-modules. This generalizes the instance
`PresheafOfModules.isMonoidal_W_inverseImage_toPresheaf`, the case of a sheaf `𝒪` with `α = 𝟙`
stated in more general universes; for `C : Type u` with `Category.{u} C`, that instance follows
from this theorem.
