# A right coefficient morphism maps the tensor-applied enveloping complex

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra, U its enveloping algebra
and C_n = ⋀[R]^n L ⊗[R] U with negative right-regular Lie coefficients. Let N, N' :
ModuleCat.{w} Uᵐᵒᵖ be right U-modules and g : N ⟶ N' a Uᵐᵒᵖ-linear morphism. Evaluating the
tensor natural transformation on envelopingComplex and mapping it over down ℕ gives
rightTensorCoefficientComplexMap : rightTensorEnvelopingComplex R L N ⟶
rightTensorEnvelopingComplex R L N'. In every degree it applies g to the balanced coefficient.
