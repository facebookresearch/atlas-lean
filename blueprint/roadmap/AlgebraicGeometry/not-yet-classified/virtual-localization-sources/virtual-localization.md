# Virtual localization

The virtual localization formula. Let $X$ be a scheme of finite type over $\mathbb{C}$ with a
$\mathbb{G}_m$-action and a $\mathbb{G}_m$-equivariant perfect obstruction theory $E$, let `D` and
`K` be cycle data and a Kresch presentation for Artin stacks of finite type over $\mathbb{C}$, and
let `P` be localization data for $X$ and $E$ (`LocalizationData`: a model of the quotient stack
$[X/\mathbb{G}_m]$ (`EquivariantSource`) with Chern data for the identity character, the ordinary
and equivariant virtual geometry of $E$, a $\mathbb{G}_m$-equivariant closed embedding of $X$ into
a smooth separated scheme of finite type over $\mathbb{C}$, the fixed scheme with its connected
components $F_j$, and for each $F_j$ its fixed obstruction theory, virtual normal bundle
$N_j^{\mathrm{vir}}$ and push-forward data along $\iota_j : F_j \to X$). Then, in the localized
equivariant Chow group (`localizationFormula`),
$[X]^{\mathrm{vir}} = \sum_j \iota_{j*}([F_j]^{\mathrm{vir}} \cap e(N_j^{\mathrm{vir}})^{-1})$.
