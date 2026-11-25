# Em Underlying Bar Iso hom app

The forward underlying comparison component in degree `n` is the whiskered
`barMap` at the module isomorphisms. This removes the `isoWhiskerRight` and
`twoSidedBarIso` unfolding: downstream `simp` with `barMap_app`,
`emModuleIso_hom_f_app`, and `emModRefl_f_app` collapses both reflexive
components to identities. Mirrors `twoSidedBarIso_hom_app_op_mk`.
