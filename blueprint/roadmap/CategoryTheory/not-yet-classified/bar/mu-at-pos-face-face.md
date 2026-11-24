# Mu At Pos face face

For a monad `T` on `C`, `X : C`, and raw left-counted indices `i, j : Fin n`
with `i ≤ j`, the two composites of monad multiplication agree:

`muAtPos T (n + 1) j.succ X ≫ muAtPos T n i X =`
`muAtPos T (n + 1) i.castSucc X ≫ muAtPos T n j X`.

These indices are not the reversed indices of the public bar faces.
