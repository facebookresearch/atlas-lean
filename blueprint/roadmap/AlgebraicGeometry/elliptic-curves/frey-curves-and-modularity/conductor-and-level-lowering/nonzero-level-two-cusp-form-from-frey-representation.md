# A nonzero level-two cusp form from modular irreducible Frey torsion

For every Frey package, if its rational Frey curve is modular in the good-prime trace-matching sense and its $p$-torsion is irreducible over $\mathbb F_p$, then there exists a nonzero complex cusp form of weight two on $\Gamma_0(2)$. The modularity assumption is part of the statement even though the cited proof rederives it.

## Depends on

- [Galois action on elliptic-curve torsion](../../galois-action-on-torsion-points/gal-rep.md)
- [Trace matching and levels](../trace-modularity-and-lifting/trace-matching-modularity-and-levels.md)

## Proof depends on

- [Realization at a Frey conductor level](residual-modularity-at-a-frey-conductor-level.md)
- [Lowering from a Frey conductor level](nonzero-level-two-cusp-form-from-frey-conductor-level.md)

## Expansion

Pass through conductor-supported residual modularity, keeping the source’s explicit modularity premise.

## Conventions

For the input carrier and the integral-to-rational comparison, see [Frey packages and their models](../trace-modularity-and-lifting/normalized-fermat-solutions-and-frey-curves.md).

For irreducibility use the [pinned invariant-submodule criterion](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/PointGaloisAction.lean#L137-L165).

## Sources

- Anthropic, [FreyPackage.level_lowering_to_two](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_level_lowering_to_two.lean#L131).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
