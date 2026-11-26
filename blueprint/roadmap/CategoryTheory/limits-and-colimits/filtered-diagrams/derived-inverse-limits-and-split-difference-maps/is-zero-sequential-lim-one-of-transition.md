# Sequential lim-one vanishes for surjective transitions

Let `R : Type u` be a ring and `A : ℕᵒᵖ ⥤ ModuleCat.{w} R` an inverse sequence whose successor
transitions are epimorphisms. Then `IsZero (sequentialLimOne A)`. This object is the cokernel
of the product difference `(a_n)_n ↦ (a_n - τ_n(a_{n+1}))_n`, where `τ_n : A_{n+1} → A_n` is
the successor map.
