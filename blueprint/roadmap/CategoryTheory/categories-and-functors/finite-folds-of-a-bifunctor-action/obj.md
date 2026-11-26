# Ordered left folds of a bifunctor

Let `C` and `D` be categories and `F : C ⥤ D ⥤ C` a bifunctor.
For `P ∈ C` and an ordered list of factors in `D`, form their left fold:
the empty list gives `P`, and folding `M :: Ms` continues from `F(P,M)`
along `Ms`. Thus three factors give `F(F(F(P,M₁),M₂),M₃)`.
