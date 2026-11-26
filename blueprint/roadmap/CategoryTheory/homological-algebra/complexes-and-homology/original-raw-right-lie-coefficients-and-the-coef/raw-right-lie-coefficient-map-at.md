# Joint right coefficient maps lift to the common carrier modules

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra and A :
RightLieModuleCat.{w} R L. Put M = toLeft A, with ⁅x,m⁆ = −A.action x m, and H = max u v v' w
w' z. Let L' : Type v' be another R-Lie algebra, f : L →ₗ⁅R⁆ L', A' : RightLieModuleCat.{w'} R
L' and g : HomOver f A A'. rawRightLieCoefficientMapAt is a HomOver f map between the two
lifted right Lie coefficients, with value ULift.up m ↦ ULift.up(g(m)).
