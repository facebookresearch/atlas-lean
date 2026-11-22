# Global Artin reciprocity

This node is still to be broken down. It covers the reciprocity law of global class field theory in
its idèlic form.

Let $K$ be a number field, $\mathbb{I}_K$ its idèle group, $C_K = \mathbb{I}_K / K^\times$ its idèle
class group and $K^{\mathrm{ab}}$ a maximal abelian extension of $K$.

1. **The global Artin map.** There is a unique continuous homomorphism
   $\phi_K \colon \mathbb{I}_K \to \mathrm{Gal}(K^{\mathrm{ab}}/K)$ such that, for every finite
   extension $L \subseteq K^{\mathrm{ab}}$ of $K$ and every place $w$ of $L$ above a place $v$ of $K$,
   the composite $K_v^\times \to \mathbb{I}_K \to \mathrm{Gal}(L/K)$ of the inclusion at $v$, of
   $\phi_K$ and of restriction to $L$ is the local Artin map
   $K_v^\times \to \mathrm{Gal}(L_w/K_v)$ followed by the inclusion of $\mathrm{Gal}(L_w/K_v)$ as the
   decomposition group of $w$. In particular, if $v$ is a finite place unramified in $L$, the idèle
   whose component at $v$ is a uniformizer of $K_v$ and whose other components are $1$ maps to the
   Frobenius element of $v$ in $\mathrm{Gal}(L/K)$.
2. **Reciprocity.** $\phi_K(K^\times) = 1$, so $\phi_K$ factors through $C_K$; and for every finite
   abelian extension $L/K$ the induced map $\phi_{L/K} \colon C_K \to \mathrm{Gal}(L/K)$ is surjective
   with kernel $\mathrm{Nm}_{L/K}(C_L)$, so that
   $C_K / \mathrm{Nm}_{L/K}(C_L) \cong \mathbb{I}_K / K^\times \mathrm{Nm}_{L/K}(\mathbb{I}_L) \cong \mathrm{Gal}(L/K)$.

A good expansion follows Milne's Chapter VII and has the following pages.

- The local Artin maps of local class field theory with their normalization at unramified places,
  and the definition of $\phi_K$ as their product (Milne, Proposition V.5.2; Sutherland,
  Definition 28.2 and Proposition 28.3), with the Frobenius compatibility at unramified places as a
  statement of its own.
- Surjectivity of $\phi_{L/K}$: the Frobenius elements at the primes outside a finite set generate
  $\mathrm{Gal}(L/K)$ (Milne, Proposition VII.4.7 and Corollary VII.4.8), deduced from the first
  inequality through Lemma VII.4.5 and Proposition VII.4.6.
- The first and second inequalities, which for cyclic extensions are the statements of
  [the cyclic case](idele-class-tate-cohomology-of-cyclic-extension.md), and the second inequality for
  all Galois extensions (Milne, Theorem VII.5.1(a), reduced to the cyclic case by Lemmas VII.5.3
  and VII.5.4).
- Triviality of $\phi_{L/K}$ on the principal idèles (Milne, Theorem VII.8.1(a)), first for
  cyclotomic extensions (Example VII.8.2 and Lemma VII.8.4), then in general through the Brauer
  group (Proposition VII.7.2 and Lemmas VII.8.5 and VII.8.6).
- The isomorphism $C_K / \mathrm{Nm}_{L/K}(C_L) \cong \mathrm{Gal}(L/K)$, from the three previous
  items and the second inequality (Milne, the paragraph after Theorem VII.8.1).

The expansion should keep as separate statements the three properties of $\phi_{L/K}$ that the
proof of the [Chebotarev density theorem](chebotarev-density-theorem.md) uses: surjectivity,
triviality on the principal idèles and Frobenius compatibility at unramified places.

## Depends on

- [Topological idele class group](adeles-and-ideles/topological-idele-class-group.md)

## Proof depends on

- [Tate cohomology of the idèle class group of a cyclic extension](idele-class-tate-cohomology-of-cyclic-extension.md)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Proposition V.5.2 and Theorem V.5.3 (the
  statement); Chapter VII, Sections 1–8 (the proof).
- A. V. Sutherland, *Number Theory I* (MIT 18.785, Fall 2021), Lecture 28, "Global class field theory,
  the Chebotarev density theorem", <https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf>:
  Definition 28.2, Proposition 28.3 and Theorem 28.4 (Global Artin Reciprocity).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, as `GroundTheory.Global.reciprocityMapEquiv`.
