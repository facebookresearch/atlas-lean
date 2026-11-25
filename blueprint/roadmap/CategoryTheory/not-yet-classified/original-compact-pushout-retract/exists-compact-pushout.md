# Exists Compact Pushout

Let `C` be χ-locally presentable at regular χ, with pushouts. Suppose
`u : D ⟶ A`, `f : D ⟶ E` and `c : E ⟶ B` form the given pushout
`H : IsPushout u f i c`, and `R : RetractArrow g i` is a given Arrow retract.
Both endpoints `D` and `E` of `f` must be χ-presentable at that same rank.
There are χ-presentable `D'` and `L`, maps `alpha : D ⟶ D'` and `v : D' ⟶ X`
with `alpha ≫ v = u ≫ R.r.left`, and `f' : D' ⟶ L` retracting the pushout
inclusion `pushout.inl alpha f` of the same `f`. The resulting square is
`IsPushout v f' g k`, and the entire replacement `Arrow.mk f'` is
χ-presentable. This is the fixed-rank form of Jacob Lurie's *Higher Topos
Theory* (author PDF, April 9, 2017), Lemma A.1.5.10, pp. 805–806.
