# Left Weyl Multiplier transvection01 inv mul weyl01 inv mul transvection01 mul weyl01 neg one

Four-factor numerator `0 ⋖ 1` Tits multiplier for `Fin 3`.
For `h01 : (0 : Fin 3) ⋖ (1 : Fin 3)` and `u : Fˣ`, the four-factor
product
`transvection h01.ne (↑u⁻¹ : F) * (weylSLUnit 0 1 h01.ne (1 : Fˣ))⁻¹ *
  transvection h01.ne (↑u : F) * weylSLUnit 0 1 h01.ne (-1 : Fˣ)`
has `leftSimpleRootCoeff = 0`, so `leftWeylMultiplier h01` is the
zero-branch value `weylHMTits F 3 0 1 h01.ne (1 : Fˣ)`. Characteristic-two
safe and valid for `u = 1` and `u = -1`; factor order and all coercions
`↑u⁻¹`, `↑u`, `(1 : Fˣ)`, `(-1 : Fˣ)` preserved as stated. No generic
multiplier or `snd` law is used; middle theorem not needed.
