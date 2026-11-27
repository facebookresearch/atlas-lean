# Irreducibility of Frey torsion

For every Frey package of prime exponent $p\ge5$, the Galois module $E[p](\overline{\mathbb Q})$ of its attached rational equation is nontrivial and has no proper nonzero invariant submodule. This is irreducibility over $\mathbb F_p$, not absolute irreducibility and not a claim about arbitrary rational elliptic curves.

## Depends on

- [Galois action on elliptic-curve torsion](../../galois-action-on-torsion-points/gal-rep.md)

## Proof depends on

- [The residue class $3$ modulo $8$](frey-irreducibility-at-three-mod-eight.md)
- [Cofixed line from reducibility](reducible-frey-torsion-has-a-cofixed-line.md)
- [Exponents at least 17](no-cofixed-line-for-large-frey-exponents.md)
- [Exponents 5, 7, and 13](no-cofixed-line-for-frey-exponents-five-seven-thirteen.md)
- [Exponent 11](no-cofixed-line-for-frey-exponent-eleven.md)

## Expansion

Align freeness, scalar extension and the absolute Galois action with the torsion API; in particular do not generalize from the normalized Frey equation to arbitrary elliptic curves.

## Conventions

For the input carrier and the integral-to-rational comparison, see [Frey packages and their models](../trace-modularity-and-lifting/normalized-fermat-solutions-and-frey-curves.md).

For irreducibility use the [pinned invariant-submodule criterion](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/PointGaloisAction.lean#L137-L165).

## Sources

- Anthropic, [FreyPackage.Mazur_Frey](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_FreyPackage_Mazur_Frey.lean#L70).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
