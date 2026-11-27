# Residual modularity at five by congruence of good-prime traces

Let $W,W'$ be integral Weierstrass models and $N$ a natural number. Suppose $W'$ is trace-matching modular at level $N$, every prime dividing $\Delta(W')$ divides $N$, and for every common good prime $\ell\ne5$ the integer $a_\ell(W')-a_\ell(W)$ is divisible by 5. Then $W$ is residually modular modulo 5 at level $N$, with the same meaning of a congruence modulo a maximal ideal above 5.

## Depends on

- [Trace matching and levels](trace-matching-modularity-and-levels.md)
- [Galois action on elliptic-curve torsion](../../galois-action-on-torsion-points/gal-rep.md)

## Expansion

Compare the existing trace and residual modularity definitions; verify that every prime tested by the conclusion is good for $W'$ using the stated discriminant support condition.

## Conventions

For irreducibility use the [pinned invariant-submodule criterion](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/PointGaloisAction.lean#L137-L165).

## Sources

- Anthropic, [WeierstrassCurve.isResiduallyModularOfLevel_of_switch](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_of_switch.lean#L5-L10).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
