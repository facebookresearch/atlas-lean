# Postcomp Comonad

The comonad on `A ⥤ C` given by postcomposition with `G`.

The underlying functor sends `L` to `L ⋙ G`; the counit and comultiplication
are `G.ε` and `G.δ` whiskered on the left. The laws follow componentwise from
the comonad laws of `G`.
