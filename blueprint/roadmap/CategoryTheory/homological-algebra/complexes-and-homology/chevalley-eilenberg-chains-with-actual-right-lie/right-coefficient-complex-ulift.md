# The right CE complex lifts to a larger module-category height

Let R : Type u be a commutative ring, L : Type v an R-Lie algebra and M :
RightLieModuleCat.{w} R L a right Lie module with action m·x = M.action x m. Let M_left have
left action ⁅x,m⁆ = −m·x. For a spare universe z, rightCoefficientComplexULift is the
degreewise image of CE_right(L,M) under ModuleCat.uliftFunctor.{z,max u v w} R, with target
height max u v w z.
