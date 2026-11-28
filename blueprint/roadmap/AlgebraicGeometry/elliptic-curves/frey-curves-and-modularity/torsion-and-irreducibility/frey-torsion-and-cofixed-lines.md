# Cofixed quotients and inertia on Frey torsion

Use the [Galois action on torsion](../../galois-action-on-torsion-points/gal-rep.md). In the source's submodule presentation, the representation acts by module endomorphisms; the [pinned point-action API](https://github.com/facebookresearch/atlas-lean/blob/099efaa6aabe39c8022e0f67e7f37ca1c8b8e7c0/MathlibExt/AlgebraicGeometry/EllipticCurve/PointGaloisAction.lean#L120-L165) sends each Galois element to that same action on points. Its irreducibility criterion requires nontrivial torsion and no proper nonzero stable submodule. This agrees with the source's irreducibility test; it is not an additional Frey-specific predicate.

A cofixed line in the source is a stable submodule $L$ that is neither zero nor the whole module and satisfies $\sigma x-x\in L$ for every Galois element $\sigma$ and torsion point $x$. The action is trivial on the **quotient**, not necessarily on $L$. Unramifiedness at $q$ means the inertia group at **every** valuation above $q$ acts trivially on the entire torsion module. This is different from requiring that its common fixed submodule be zero.

## Depends on

- [Galois action on elliptic-curve torsion](../../galois-action-on-torsion-points/gal-rep.md)

## Expansion

Build the cofixed-quotient and unramifiedness predicates on the pinned point action. Use its invariant-submodule criterion for irreducibility rather than introducing a second torsion action or irreducibility definition. Verify the quotient condition and inertia restriction on the same torsion module.

## Sources

- Anthropic, [stability and irreducibility](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_FLTPrelim_GaloisRep.lean#L66-L77).
- Anthropic, [the cofixed quotient predicate](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_FLTPrelim_CofixedLine.lean#L13-L18).
- Anthropic, [the Frey action](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_FreyPackage_GaloisRep.lean#L18-L42) and [unramifiedness](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_FLTPrelim_Ramification.lean#L35-L48).
