# Sequential lim-one vanishes for eventually surjective transitions

Let `R : Type u` be a ring and `A : ℕᵒᵖ ⥤ ModuleCat.{w} R`. Assume there exists `N : ℕ` such
that every successor transition `A_{n+1} → A_n` is an epimorphism for `n ≥ N`. Then `IsZero
(sequentialLimOne A)`, the cokernel of the product difference `a_n-τ_n(a_{n+1})`.
