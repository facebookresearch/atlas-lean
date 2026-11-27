# Coinvariants form a functor in the exterior-tensor universe

Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. The functor LieModuleCat.{w} R L ⥤ ModuleCat.{max u v w} R sends X to ULift.{max u
v w} (X/[L,X]). Its map for f : X ⟶ Y sends ULift.up [m] to ULift.up [f(m)], using the induced
coinvariant quotient map.
