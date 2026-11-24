# Stage Eval Naturality Iso General

Evaluation naturality, degree-generic: evaluating after `mapStage` agrees
with postcomposition after evaluation. The proof uses only `mapStage_obj/map`
(`rfl`), pointwise `eval`, and functor-comp associativity, so it never uses
interval structure or any `n = 2` fact. Components are `eqToIso (by rfl)`;
both composites send `X` to `F.obj (X.obj.obj a)` and `φ` to
`F.map (((forget C n).map φ).app a)`.
