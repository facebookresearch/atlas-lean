---
article_id: af_7faa79e8dfe1440f8d0ab1ec
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.cube_lattice_paths_card_eq_colored_motzkin_card
---

# Cube lattice paths card eq colored motzkin card

Lattice paths in the cubic lattice and colored Motzkin paths.

The formalization is the paper's theorem at dimension `n + 1`: both sides
use `2 * n` flat-step colors, and only the distinguished coordinate is
constrained to a Dyck bridge. Both sides equal
`ULDMotzkin.uldMotzkinNumber 1 (fun _ => 1) (2 * n) (fun _ => 1) le_rfl k`; see
`cube_lattice_paths_card_eq_uldMotzkinNumber`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Motzkin Path](../../part-09/uldmotzkin-number-of-rank-r/is-motzkin-path.md)
- [ULDMotzkin Step](../../part-09/uldmotzkin-number-of-rank-r/uldmotzkin-step.md)
- [Path Height](../../part-09/uldmotzkin-number-of-rank-r/path-height.md)
- [Step Height](../../part-09/uldmotzkin-number-of-rank-r/step-height.md)
- [Uld Motzkin Number](../../part-09/uldmotzkin-number-of-rank-r/uld-motzkin-number.md)
- [Uld Motzkin Number eq card](../../part-09/uldmotzkin-number-of-rank-r/uld-motzkin-number-eq-card.md)
- [Cube lattice paths card eq uld Motzkin Number](cube-lattice-paths-card-eq-uld-motzkin-n.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.CubicLatticeColoredMotzkin](../../../../../../../sources/v2/MathlibExt.md)
- Rigoberto Flórez, Leandro Junes, and José L. Ramírez, "Further Results on Paths in an n-Dimensional Cubic Lattice," Journal of Integer Sequences 21 (2018), Article 18.1.2, Theorem (label bijection:Motzkin), lines 924–926, https://cs.uwaterloo.ca/journals/JIS/VOL21/Florez/florez4.tex
