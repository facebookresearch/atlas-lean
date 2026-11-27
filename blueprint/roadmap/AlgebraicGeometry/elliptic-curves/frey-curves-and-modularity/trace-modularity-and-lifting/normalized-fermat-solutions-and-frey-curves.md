# Normalized Fermat solutions and Frey curves

The [normalization step](../../exists-of-fermat-counterexample.md) starts from a raw Fermat counterexample and produces a package. The later modularity and level-lowering arguments instead start with that package already supplied. The package and its two model constructions use the [same carrier and equations](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/FreyCurve.lean#L65-L100) throughout.

For the passage from the integral equation to the rational one, the relevant fact is that the integer quotients in the integral coefficients are exact. Thus casting the integral coefficients to the rationals gives the rational model; replacing the integer division by rational division without this divisibility check would not justify the passage. See the [coefficient comparison](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/FreyCurve.lean#L136-L171) and the [semistability result for the integral equation](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/FreyCurve.lean#L286-L293).

## Sources

- Anthropic, [the source's Frey package and equations](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_FLTPrelim_FreyPackage.lean).
