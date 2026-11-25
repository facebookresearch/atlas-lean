# Precomp Comonad

The comonad on `C ⥤ D` given by precomposition with `G`.

The underlying functor sends `R` to `G ⋙ R`; the counit and comultiplication
are `G.ε` and `G.δ` whiskered on the right. The laws follow componentwise from
the comonad laws of `G`.
