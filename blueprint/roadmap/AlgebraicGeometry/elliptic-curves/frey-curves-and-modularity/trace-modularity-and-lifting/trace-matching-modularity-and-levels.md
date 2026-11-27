# Trace matching and residual modularity for integral models

Use the existing [semistability predicate](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/FreyCurve.lean#L55-L58), [integral-model relation](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/SemistableModel.lean#L88-L92), and [good-prime trace and residual modularity predicates](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/ResidualModularity.lean#L103-L133). For normalized forms, use the [four width-one Fourier-coefficient conditions](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/ResidualModularity.lean#L77-L97), with no additional Hecke eigenvector condition.

In the source's complex trace-matching condition at level $N$, a normalized weight-two cusp form on $\Gamma_0(N)$ has prime-indexed coefficient equal to the model's Frobenius trace at each good prime not dividing $N$. For a rational equation, the source requires an integral model of it and such a form at some positive level. For a Frey package with exponent $p$, a residual realization at a *specified* $N$ amounts to the existence of an integral model of its rational curve that is residually modular at $(p,N)$. It imposes the base residual predicate's good-prime congruences, not exact complex trace equality, and does not identify the two Galois representations.

An admissible Frey conductor level is a positive squarefree $N$ whose prime divisors divide $abc$; not every prime dividing $abc$ has to occur. The exact-level predicate for an integral model requires a positive squarefree level with exactly the primes dividing its discriminant, at which the complex trace matching holds. Neither predicate is the [conductor radical of a given integral model](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/SemistableModel.lean#L60-L86): the Frey support condition allows omissions, whereas an exact-level modularity statement requires the cusp-form realization as well as the support equality.

## Depends on

- [Frobenius trace of the reduction](../../point-counts-and-frobenius-traces/frobenius-trace.md)

## Expansion

State the model-existence wrappers over the pinned definitions: complex trace matching at a level, the rational-curve version, the specified-level Frey residual condition, and its conductor support. Separate exact support from the weaker containment condition. The base trace and residual predicates do not supply those witnesses or construct the integral models.

## Sources

- Anthropic, [trace matching and model existence](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_FLTPrelim_Modularity.lean#L76-L102).
- Anthropic, [Frey and integral-model residual congruences](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_FLTPrelim_ModularRep.lean#L62-L87).
- Anthropic, [admissible Frey conductor levels](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_FreyPackage_IsConductorLevel.lean#L8-L14).
- Anthropic, [the exact-conductor modularity predicate](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_WeierstrassCurve_Mlc1RowStatement.lean#L9-L16).
