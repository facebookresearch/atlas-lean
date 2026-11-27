# Removing the residual prime from a Frey level

Let a Frey package have residual prime $p$. Suppose $N$ is an admissible Frey conductor level, $p\mid N$, its $p$-torsion is irreducible, and its representation is realized by the stated trace congruences at level $N$. Then some natural $M$ divides $N$, is not divisible by $p$, and realizes those congruences at level $M$.

## Depends on

- [Galois action on elliptic-curve torsion](../../galois-action-on-torsion-points/gal-rep.md)
- [Trace matching and levels](../trace-modularity-and-lifting/trace-matching-modularity-and-levels.md)

## Expansion

Isolate the at-$p$ finite local condition and the level-lowering argument; do not replace the witness $M$ by the specific quotient $N/p$.

## Conventions

For the input carrier and the integral-to-rational comparison, see [Frey packages and their models](../trace-modularity-and-lifting/normalized-fermat-solutions-and-frey-curves.md).

For irreducibility use the [pinned invariant-submodule criterion](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/PointGaloisAction.lean#L137-L165).

## Sources

- Anthropic, [FreyPackage.level_lowering_at_p_of_conductorLevel](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_level_lowering_at_p_of_conductorLevel.lean#L70).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
