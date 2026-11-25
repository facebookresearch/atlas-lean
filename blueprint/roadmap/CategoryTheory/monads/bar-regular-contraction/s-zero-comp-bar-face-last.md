# S zero comp bar Face last

Degree-zero extra-degeneracy law: `s₀ ≫ d₁ = pairing ≫ s'`.

At degree zero the successor comparison `barObj_obj_succ_eq L 0 a` is `congrArg T.obj
(monadPow_obj_T_comm T 0 _)` with `monadPow_obj_T_comm T 0 _ = rfl`.  Hence `barObj T... L 1`
object equals `T.obj (barObj T... L 0).obj` by `rfl`.  We `cases` on that object equality – an
honest use of reflexivity at degree zero – making `B₁` and `T(B₀)` definitionally equal, so
`barObj_obj_succ_eq` becomes `rfl` and `eqToHom rfl = 𝟙` via `rfl`.  Then `s L 0` reduces to
`η_{B₀}` by `comp_id`.  The face `d₁ = barFace 0 1` is the last face, i.e. `T.map (L.action)`, by
`barFaceApp_of_val_last` and `rfl`.  The equality becomes `η ≫ T.map action = action ≫ η`, which
is `T.η.naturality (L.action.app a)`.
