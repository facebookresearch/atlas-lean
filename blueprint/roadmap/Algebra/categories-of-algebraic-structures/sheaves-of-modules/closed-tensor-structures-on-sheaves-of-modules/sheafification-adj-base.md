# Base module-sheafification adjunction

Let `(C,J)` be a site at universe `u`, `R : Sheaf J CommRingCat.{u}`, and assume weak additive
sheafification, the locally-bijective comparison, and the underlying-ring sheaf comparison.
The adjunction `sheafificationAdjBase R` is `sheafificationBase R ⊣ forgetRestrictBase R`,
formed using the identity ring comparison `Sheaf.commRingCatForget₂Id R`.
