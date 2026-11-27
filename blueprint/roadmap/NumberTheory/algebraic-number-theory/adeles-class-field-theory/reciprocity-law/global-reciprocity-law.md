# Global reciprocity law

Let $K$ be a number field with idèle class group $C_K = \mathbb{I}_K / K^\times$, and let
$\phi_K \colon \mathbb{I}_K \to \mathrm{Gal}(K^{\mathrm{ab}}/K)$ be its
[global Artin map](global-artin-map.md), with $\phi_{L/K}(a) = \phi_K(a)|_L$. Then:

1. $\phi_K(K^\times) = 1$, so $\phi_K$ factors through $C_K$;
2. for every finite abelian extension $L/K$, $\phi_{L/K}$ induces an isomorphism

    $$\mathbb{I}_K / K^\times \mathrm{Nm}_{L/K}(\mathbb{I}_L) \xrightarrow{\ \sim\ } \mathrm{Gal}(L/K),$$

    where $\mathrm{Nm}_{L/K} \colon \mathbb{I}_L \to \mathbb{I}_K$ is the idèle norm,
    $\mathrm{Nm}_{L/K}(b)_v = \prod_{w \mid v} \mathrm{Nm}_{L_w/K_v}(b_w)$; equivalently, an isomorphism
    $C_K / \mathrm{Nm}_{L/K}(C_L) \to \mathrm{Gal}(L/K)$. In particular
    $(C_K : \mathrm{Nm}_{L/K}(C_L)) = [L : K]$.

Milne's proof (the paragraph after Theorem VII.8.1). Part 1 is the
[triviality on principal idèles](artin-map-trivial-on-principal-ideles.md). The norms lie in the kernel by
the [norm compatibility](norm-compatibility.md), so $\phi_{L/K}$ induces a homomorphism
$\mathbb{I}_K / K^\times \mathrm{Nm}_{L/K}(\mathbb{I}_L) \to \mathrm{Gal}(L/K)$. It is surjective: an idèle
that is a uniformizer at a finite place $v$ unramified in $L$ and $1$ elsewhere maps to the Frobenius
element of $v$ ([the global Artin map at unramified places](artin-map-at-unramified-places.md)), and these
Frobenius elements generate $\mathrm{Gal}(L/K)$ ([Frobenius elements generate](../cohomology-of-idele-classes/frobenius-elements-generate.md)).
It is injective because the source has order at most $[L : K]$, by the
[second inequality](../cohomology-of-idele-classes/second-inequality.md). The form with idèle class groups
comes from the [Galois invariants of the idèle class group](../cohomology-of-idele-classes/galois-invariants-of-idele-classes.md).

## Depends on

- [Global Artin map](global-artin-map.md)
- [Topological idele class group](../adeles-and-ideles/topological-idele-class-group.md)

## Proof depends on

- [The global Artin map is trivial on principal idèles](artin-map-trivial-on-principal-ideles.md)
- [Norm compatibility of the global Artin map](norm-compatibility.md), for the norms in the kernel
- [The global Artin map at unramified places](artin-map-at-unramified-places.md), for the image of a uniformizer at an unramified place
- [Frobenius elements generate the Galois group of a solvable extension](../cohomology-of-idele-classes/frobenius-elements-generate.md), for the surjectivity
- [Second inequality of global class field theory](../cohomology-of-idele-classes/second-inequality.md), for the injectivity
- [Galois invariants of the idèle class group](../cohomology-of-idele-classes/galois-invariants-of-idele-classes.md), for the form with idèle class groups

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Theorem V.5.3 (Reciprocity Law, the statement) and
  the paragraph after it; Theorem VII.8.1 and the paragraph after it (the proof).
- A. V. Sutherland, *Number Theory I* (MIT 18.785, Fall 2021), Lecture 28, "Global class field theory,
  the Chebotarev density theorem", <https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf>:
  Theorem 28.4 (Global Artin Reciprocity).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, as `GroundTheory.Global.reciprocityMapEquiv`.
