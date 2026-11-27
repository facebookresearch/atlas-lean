# Submodule Quotient Equiv

Linear equivalence between the preserved additive quotient
`DegreeMod F n ℓ` and the submodule quotient
`(degree F n) ⧸ ellMultiplesSubmodule F n ℓ`. It is obtained from the
identity additive equivalence via `QuotientAddGroup.congr` and
`AddEquiv.toIntLinearEquiv`; the subgroup equality uses
`AddSubgroup.toIntSubmodule_toAddSubgroup`.
