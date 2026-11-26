# Modularity lifting at three with a conditional inertia constraint

Let $W/\mathbb Z$ be semistable with $\Delta\ne0$ and irreducible $p$-torsion. Assume a positive $M_0$ at which $W$ is residually modular modulo $p$, and that $q^3\nmid M_0$ for every prime $q\ne p$. Take $p=3$. If $p^2\mid M_0$, require the following inertia condition at $p$. For every valuation subring of $\overline{\mathbb Q}$ lying over the indicated prime, the only torsion point of that order fixed by every member of the inertia group is zero. Then $W$ is modular in the trace-matching sense at some positive squarefree level with precisely the prime divisors of $\Delta(W)$.

## Depends on

- [Trace matching and levels](trace-matching-modularity-and-levels.md)
- [Galois action on elliptic-curve torsion](../../galois-action-on-torsion-points/gal-rep.md)

## Proof depends on

- [Hecke surjection](surjection-from-a-deformation-ring-to-a-hecke-algebra.md)
- [Taylor–Wiles patching datum](../../../../NumberTheory/modular-forms-q-series/modular-forms/taylor-wiles-patching/patching-datum.md)

## Expansion

Specify the local deformation type and lift the residual datum at the allowed levels; separate the surjection from the subsequent patching and exact-conductor trace matching.

## Conventions

Irreducibility uses the [pinned invariant-submodule criterion](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/PointGaloisAction.lean#L137-L165). The condition at three concerns a **zero common fixed submodule** for each inertia group, not triviality of its action.

## Sources

- Anthropic, [WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd.lean#L120-L129).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
