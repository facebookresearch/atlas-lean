# CE homology is a functor of the coefficient Lie module

Let R : Type u be a commutative ring and L : Type v an R-Lie algebra with its Lie ring
structure. For each n : ℕ, coefficientHomologyFunctor R L n sends X : LieModuleCat.{w} R L to
H_n(coefficientComplex R L X), in ModuleCat.{max u v w} R. It sends a coefficient morphism to
the degree-n homology map of its induced CE chain map.
