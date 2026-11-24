# Reciprocal parameterization

When the branch saturation currents satisfy
`alphaF * IsF = alphaR * IsR`, both derive from the single transport saturation
current `IS = alphaF * IsF`: `IsF = IS / alphaF` and `IsR = IS / alphaR`. The
collector and emitter-out currents then depend on `IsF`, `IsR` only through `IS`,
in transport form. This is a parameterization equivalence: it does not derive
reciprocity from device physics, it states what reciprocity means for the
currents. The `_of_transportSaturation` lemmas below use the parameterization
directly.
