# The coefficient-first balanced Koszul complex

Let k : Type u and R : Type v be commutative rings with R a k-algebra. Let V : Type w be an
R-module, and let M : Type z have k- and Rᵐᵒᵖ-module structures. For x : V →ₗ[R] R, define
balancedCoefficientComplex k R V M x by applying N ↦ B k R M N to the Koszul complex on V and
x. Its degree-n object is B k R M (⋀[R]^n V), in ModuleCat.{max v w z} k, with shape down ℕ.
