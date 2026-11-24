# Horseshoe

The injective horseshoe from explicit endpoint resolutions.

Informal sketch: apply the projective horseshoe in `Cᵒᵖ`, unop the middle
resolution (`projectiveResolutionUnopInj`) and the SES maps (swapping
inclusion/projection since `unop` reverses arrows). Augmentation compatibilities
are the unop'd op-side ones; the proofs need `single₀`-naturality of
`single₀UnopIso` through `op` (`HorseshoeData.single₀UnopIso_naturality`).
