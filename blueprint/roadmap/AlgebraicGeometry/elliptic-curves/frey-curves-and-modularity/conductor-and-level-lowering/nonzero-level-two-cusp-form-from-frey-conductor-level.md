# A nonzero level-two cusp form from a conductor-supported Frey level

Assume a Frey package has irreducible $p$-torsion. If some specified $N$ is an admissible Frey conductor level and its trace congruences are realized at level $N$, there is a nonzero weight-two cusp form on $\Gamma_0(2)$.

## Depends on

- [Galois action on elliptic-curve torsion](../../galois-action-on-torsion-points/gal-rep.md)
- [Trace matching and levels](../trace-modularity-and-lifting/trace-matching-modularity-and-levels.md)

## Proof depends on

- [Removing the residual prime](lowering-the-residual-prime-in-a-frey-level.md)
- [Removing an unramified odd prime](lowering-an-odd-prime-in-a-frey-level.md)
- [Weight-two cusp forms vanish at level one](../../../../NumberTheory/modular-forms-q-series/modular-forms/weight-two-cusp-forms-on-2/s2-gamma0-one-eq-zero.md)

## Expansion

Iterate prime removal with squarefree level and condition the final step on the level-one vanishing theorem.

## Conventions

For the input carrier and the integral-to-rational comparison, see [Frey packages and their models](../trace-modularity-and-lifting/normalized-fermat-solutions-and-frey-curves.md).

For irreducibility use the [pinned invariant-submodule criterion](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/PointGaloisAction.lean#L137-L165).

## Sources

- Anthropic, [FreyPackage.level_lowering_to_two_of_conductorLevel](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_level_lowering_to_two_of_conductorLevel.lean#L91).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
