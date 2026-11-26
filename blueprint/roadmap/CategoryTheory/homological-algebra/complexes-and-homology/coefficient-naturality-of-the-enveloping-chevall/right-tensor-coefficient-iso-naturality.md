# Balanced cancellation coordinates commute with right coefficient maps

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Let N, N' :
ModuleCat.{w} Uᵐᵒᵖ be right U-modules and g : N ⟶ N' a Uᵐᵒᵖ-linear morphism. Let e_N and e_N'
be the isomorphisms from the balanced tensor complexes to CE with rightCoefficients, whose Lie
action is ⁅x,n⁆ = −op(ι(x)) • n. Then rightTensorCoefficientComplexMap g ≫ e_N'.hom = e_N.hom
≫ coefficientComplexMap(rightCoefficientsMap g). The coordinate map sends [n,w⊗a] to w⊗(op a •
n).
