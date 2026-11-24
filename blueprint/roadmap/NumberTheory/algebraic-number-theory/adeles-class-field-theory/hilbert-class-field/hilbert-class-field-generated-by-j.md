# The j-invariant of a CM lattice generates the Hilbert class field

Let $K \subset \mathbb{C}$ be an imaginary quadratic field with ring of integers $\mathcal{O}_K$, and
let $\Lambda \subset \mathbb{C}$ be a lattice whose [endomorphism ring](../../../../Analysis/special-functions/elliptic-functions/complex-multiplication-of-period-lattices/endomorphism-ring.md)
$\{a \in \mathbb{C} : a\Lambda \subseteq \Lambda\}$ is $\mathcal{O}_K$, equivalently an elliptic curve
$E = \mathbb{C}/\Lambda$ with complex multiplication by $\mathcal{O}_K$. Then the field
$K(j(\Lambda))$ generated over $K$ by the $j$-invariant of $E$ is a Hilbert class field of $K$: it is
a finite abelian extension of $K$, unramified at every prime and at every infinite place, and every
such extension of $K$ embeds in it over $K$. In particular $[K(j(\Lambda)) : K]$ is the class number
$h_K$.

The lattices with endomorphism ring $\mathcal{O}_K$ are, up to homothety, the fractional ideals
$\mathfrak{a}$ of $K$ (Milne, Propositions 12.3 and 12.6), so one may take $\Lambda = \mathfrak{a}$.

Milne proves this together with the [Artin action on the $j$-invariants](artin-action-on-cm-j-invariants.md)
(his Theorem 12.18). The statement also follows from that action. Let $H \subset \mathbb{C}$ be a
Hilbert class field of $K$, which exists by the [existence theorem](../existence-theorem/existence-of-class-fields.md);
then $j(\mathfrak{a}) \in H$. An element $\mathrm{art}_{H/K}(\mathfrak{b})$ of $\mathrm{Gal}(H/K)$
fixes $j(\mathfrak{a})$ exactly when $j(\mathfrak{b}^{-1}\mathfrak{a}) = j(\mathfrak{a})$, that is,
when $\mathfrak{b}$ is principal, and by [reciprocity](../reciprocity-law/global-reciprocity-law.md) the Artin map
of $H/K$ is surjective with kernel the principal ideals. So only the identity of $\mathrm{Gal}(H/K)$
fixes $j(\mathfrak{a})$, and $K(j(\mathfrak{a})) = H$ by Galois theory. (This deduction is written
out here; it is not Milne's text.)

## Depends on

- [Hilbert class field of a number field](is-hilbert-class-field.md)
- [Endomorphism ring of a period lattice](../../../../Analysis/special-functions/elliptic-functions/complex-multiplication-of-period-lattices/endomorphism-ring.md)

## Proof depends on

- [Artin symbols act on the j-invariants of CM lattices](artin-action-on-cm-j-invariants.md)
- [Global reciprocity law](../reciprocity-law/global-reciprocity-law.md), for the Artin map of $H/K$ being surjective with kernel the principal ideals
- [The global Artin map at unramified places](../reciprocity-law/artin-map-at-unramified-places.md), which identifies the global Artin map of $H/K$ with its Artin map on ideals
- [Existence theorem of global class field theory](../existence-theorem/existence-of-class-fields.md), for the existence of a Hilbert class field, the class field of the idèles that are units at all finite places, whose norm group makes the kernel of the Artin map of $H/K$ the group of principal ideals

## Sources

- J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (2017),
  <https://www.jmilne.org/math/CourseNotes/MF.pdf>, Chapter 12: Theorem 12.18 (a) ("For any elliptic
  curve $E$ over $\mathbb{C}$ with complex multiplication by $\mathcal{O}_K$, $K[j(E)]$ is the Hilbert
  class field of $K$") and its proof, which omits the proof of Proposition 12.21 (the class group acts
  simply transitively on the geometric isomorphism classes of curves with complex multiplication by
  $\mathcal{O}_K$) over fields other than $\mathbb{C}$ ("a key point"); Propositions 12.3 and 12.6.
- J. S. Milne, *Complex Multiplication*, version 0.10 (2020),
  <https://www.jmilne.org/math/CourseNotes/CM.pdf>, Preface: the statement as the first result of the
  theory, due to Kronecker and Weber.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, as `GroundTheory.Global.Elliptic.adjoin_j_eq_hilbertClassField`.
