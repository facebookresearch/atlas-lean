# Concatenated factors compose morphism folds

For a bifunctor `F : C ⥤ D ⥤ C`, a morphism `f : P → Q` and lists
`Ms`, `Ns` in `D`, the morphism obtained by folding along `Ms ++ Ns`
agrees with first folding `f` along `Ms` and then folding that morphism
along `Ns`, after the source and target objects are identified by the
append formula for the fold.
