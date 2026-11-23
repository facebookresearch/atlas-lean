# Normal basis theorem

Let $L/K$ be a finite Galois extension of fields with Galois group $G = \operatorname{Gal}(L/K)$. Then $L$ has a
basis over $K$ indexed by $G$ that is an orbit of $G$: there is an element $x \in L$ such that the family
$(\sigma(x))_{\sigma \in G}$ is a basis of the $K$-vector space $L$.

## Sources

- Mathlib (pinned at 56a005855ea17e0b0958f73ec801ae140b0a1679), `Mathlib/FieldTheory/Galois/NormalBasis.lean`,
  lines 121–128: `IsGalois.normalBasis` ("Given a finite Galois extension `L/K`, `normalBasis K L` is a basis of `L`
  over `K` that is an orbit under the Galois group action") and `IsGalois.normalBasis_apply`
  (`normalBasis K L e = e (normalBasis K L 1)`).
