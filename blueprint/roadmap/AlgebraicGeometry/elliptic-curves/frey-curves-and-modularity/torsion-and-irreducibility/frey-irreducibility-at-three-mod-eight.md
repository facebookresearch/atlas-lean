# Frey irreducibility for an odd coordinate congruent to three modulo eight

For a Frey package with $a\equiv3\pmod8$, its rational Frey curve has nontrivial irreducible mod-$p$ torsion over $\overline{\mathbb Q}$ with the natural absolute Galois action. The congruence is in addition to the package normalization.

## Depends on

- [Galois action on elliptic-curve torsion](../../galois-action-on-torsion-points/gal-rep.md)

## Expansion

Isolate the local argument at two for this residue class; compare its reduction and inertia conventions with the torsion module.

## Conventions

For the input carrier and the integral-to-rational comparison, see [Frey packages and their models](../trace-modularity-and-lifting/normalized-fermat-solutions-and-frey-curves.md).

For irreducibility use the [pinned invariant-submodule criterion](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/PointGaloisAction.lean#L137-L165).

## Sources

- Anthropic, [FreyPackage.Mazur_Frey_of_a_mod_eight](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_Mazur_Frey_of_a_mod_eight.lean#L12-L14).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
