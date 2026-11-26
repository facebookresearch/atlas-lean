# Modularity lifting at three or five when the residual level is not divisible by the square of the residual prime

Let $W/\mathbb Z$ be semistable with $\Delta\ne0$ and irreducible $p$-torsion. Assume a positive $M_0$ at which $W$ is residually modular modulo $p$, and that $q^3\nmid M_0$ for every prime $q\ne p$. Take $p=3$ or $p=5$ and require $p^2\nmid M_0$. Then $W$ is modular in the trace-matching sense at some positive squarefree level with precisely the prime divisors of $\Delta(W)$.

## Depends on

- [Trace matching and levels](trace-matching-modularity-and-levels.md)
- [Galois action on elliptic-curve torsion](../../galois-action-on-torsion-points/gal-rep.md)

## Proof depends on

- [Hecke surjection](surjection-from-a-deformation-ring-to-a-hecke-algebra.md)
- [Taylor–Wiles patching datum](../../../../NumberTheory/modular-forms-q-series/modular-forms/taylor-wiles-patching/patching-datum.md)

## Expansion

Specify the local deformation type and lift the residual datum at the allowed levels; separate the surjection from the subsequent patching and exact-conductor trace matching.

## Conventions

For irreducibility use the [pinned invariant-submodule criterion](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/PointGaloisAction.lean#L137-L165).

## Sources

- Anthropic, [WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd.lean#L120-L125).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
