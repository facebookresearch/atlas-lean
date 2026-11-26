# Trace-matching modularity of a semistable integral model

Let $W/\mathbb Z$ be a Weierstrass equation with $\Delta(W)\ne0$ and with no prime dividing both $\Delta(W)$ and $c_4(W)$. The rational equation obtained by extending scalars is modular in the stated trace-matching sense: it has an integral model after rational change of variables with a weight-two cusp form with the specified coefficient conditions matching its good-prime traces away from a positive level. This does not state an equality of $L$-functions or a modular parametrization.

## Depends on

- [Trace matching and levels](trace-matching-modularity-and-levels.md)
- [Galois action on elliptic-curve torsion](../../galois-action-on-torsion-points/gal-rep.md)

## Proof depends on

- [Irreducibility at three or five](../torsion-and-irreducibility/irreducibility-at-three-or-five-for-semistable-models.md)
- [Residual modularity at three](residual-modularity-at-three-with-inertia-and-level-conditions.md)
- [Lifting with an inertia constraint](modularity-lifting-at-three-with-an-inertia-condition.md)
- [Lifting when the residual prime squared does not divide the level](modularity-lifting-at-three-or-five-with-nonsquare-residual-level.md)
- [A second model for the switch](semistable-three-five-switch-by-trace-congruence.md)
- [Modularity transferred by traces](residual-modularity-at-five-by-trace-congruence.md)

## Expansion

Follow the two cases of mod-3 irreducibility, using the 3–5 switch when necessary; keep the exact-level lifting conclusions distinct from the headline.

## Conventions

For irreducibility use the [pinned invariant-submodule criterion](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/PointGaloisAction.lean#L137-L165).

## Sources

- Anthropic, [WeierstrassCurve.modularity_of_semistableModel](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_WeierstrassCurve_modularity_of_semistableModel.lean#L131).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
