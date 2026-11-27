# A semistable 3–5 switch by congruence of traces

For a semistable $W/\mathbb Z$ with $\Delta(W)\ne0$ and irreducible 5-torsion there exists a semistable integral model $W'$ with $\Delta(W')\ne0$, irreducible 3-torsion, and $5\mid a_\ell(W')-a_\ell(W)$ for every prime $\ell\ne5$ good on both models. The conclusion about these models is stated as a trace congruence, not as a 5-torsion isomorphism.

## Depends on

- [Frobenius traces](../../point-counts-and-frobenius-traces/frobenius-trace.md)
- [Galois action on elliptic-curve torsion](../../galois-action-on-torsion-points/gal-rep.md)

## Expansion

Isolate the explicit 5-torsion family and its local specialization preserving the common good-prime trace congruences.

## Conventions

Use the [pinned good-prime and integral-model trace conventions](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/ResidualModularity.lean#L103-L116).

Semistability uses the [pinned integral-model predicate](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/FreyCurve.lean#L55-L58).

For irreducibility use the [pinned invariant-submodule criterion](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/PointGaloisAction.lean#L137-L165).

## Sources

- Anthropic, [WeierstrassCurve.threeFiveSwitchCurve](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_threeFiveSwitchCurve.lean#L16).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
