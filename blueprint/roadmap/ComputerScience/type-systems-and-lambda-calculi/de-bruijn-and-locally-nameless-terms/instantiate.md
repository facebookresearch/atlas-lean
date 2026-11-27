# β-substitution

`instantiate body arg` is the contractum of the redex `app (lam body) arg`:
the index `0` of `body` becomes `arg`, and every larger free index of `body` is lowered by one.
