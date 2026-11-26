# Irreducibility at three or five for a semistable integral model

If $W/\mathbb Z$ is semistable with $\Delta\ne0$, then at least one of its mod-3 and mod-5 torsion representations is irreducible over the corresponding prime field. This does not select which of the two is irreducible.

## Depends on

- [Galois action on elliptic-curve torsion](../../galois-action-on-torsion-points/gal-rep.md)

## Proof depends on

- [Four possible $j$-invariants with both reducible](four-j-invariants-of-a-model-with-reducible-three-and-five-torsion.md)

## Expansion

Rule out the four rational $j$-values using semistability of the given integral equation.

## Conventions

Semistability uses the [pinned integral-model predicate](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/FreyCurve.lean#L55-L58).

For irreducibility use the [pinned invariant-submodule criterion](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/PointGaloisAction.lean#L137-L165).

## Sources

- Anthropic, [WeierstrassCurve.modThreeOrFiveIrreducible](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_modThreeOrFiveIrreducible.lean#L15).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
