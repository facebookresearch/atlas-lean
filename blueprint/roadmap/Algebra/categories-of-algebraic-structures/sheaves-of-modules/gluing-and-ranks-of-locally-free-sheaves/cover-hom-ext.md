# Cover Hom ext

Uniqueness: two sheaf morphisms agreeing on a cover are equal. By
`SheafOfModules.hom_ext` + `PresheafOfModules.hom_ext` it suffices to check
per-open, per-section, where both sides restrict (by naturality) to the
agreed values on the trace cover — closed by `locally_eq`.
