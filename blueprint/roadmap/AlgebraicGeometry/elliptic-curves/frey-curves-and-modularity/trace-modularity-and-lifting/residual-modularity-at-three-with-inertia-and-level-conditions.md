# Residual modularity at three with level and inertia constraints

Let $W/\mathbb Z$ have nonzero discriminant, be semistable, and have irreducible 3-torsion. Then there exists $M>0$ at which $W$ is residually modular modulo 3, no prime $q\ne3$ has $q^3\mid M$, and if $9\mid M$ the following inertia condition holds at 3. For every valuation subring of $\overline{\mathbb Q}$ lying over the indicated prime, the only torsion point of that order fixed by every member of the inertia group is zero.

## Depends on

- [Galois action on elliptic-curve torsion](../../galois-action-on-torsion-points/gal-rep.md)

## Proof depends on

- [Weight-one trace realization](weight-one-traces-for-a-lift-of-a-surjective-mod-three-representation.md)

## Expansion

Separate the explicit weight-one case, the weight-two congruence lift and the local argument controlling the residual level and inertia-fixed subgroup.

## Conventions

Use the [pinned residual modularity predicate](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/ResidualModularity.lean#L118-L128) at the specified level.

Irreducibility uses the [pinned invariant-submodule criterion](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/PointGaloisAction.lean#L137-L165). The condition at three concerns a **zero common fixed submodule** for each inertia group, not triviality of its action.

## Sources

- Anthropic, [WeierstrassCurve.isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel.lean#L57-L66).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
