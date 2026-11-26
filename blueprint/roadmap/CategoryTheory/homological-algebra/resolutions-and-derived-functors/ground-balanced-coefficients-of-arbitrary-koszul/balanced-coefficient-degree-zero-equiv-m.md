# The degree-zero balanced class is evaluated by its exterior scalar

Let k : Type u and R : Type v be commutative rings with R a k-algebra. Let V : Type w be an
R-module, and let M : Type z have k- and Rᵐᵒᵖ-module structures. Assume the scalar tower k →
Rᵐᵒᵖ → M. For x : V →ₗ[R] R, m : M and a : ⋀[R]^0 V, balancedCoefficientDegreeZeroEquiv sends
[m, a] to op(exteriorPower.zeroEquiv R V a) • m.
