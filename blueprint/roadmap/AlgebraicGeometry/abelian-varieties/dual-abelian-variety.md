# Dual abelian variety

Let $A$ be an [abelian variety](abelian-scheme.md) over a field $k$, with zero $0$. Its Picard
functor $\mathcal{P}ic_{A/k}$ sends a $k$-scheme $T$ to the group of isomorphism classes of line
bundles on $A \times T$ rigidified along $\{0\} \times T$, that is, with an isomorphism
$\mathcal{O}_T \cong L|_{\{0\} \times T}$. Let $\operatorname{Pic}^0(A)$ be the group of isomorphism
classes of line bundles $L$ on $A$ such that $t_a^* L \cong L$ on $A_{\bar k}$ for every $a \in
A(\bar k)$, where $\bar k$ is an algebraic closure of $k$ and $t_a$ is translation by $a$;
equivalently $m^* L \cong p^* L \otimes q^* L$ on $A \times A$, with $m$ the group law and $p$, $q$
the projections.

1. (Dual abelian variety.) The functor $\mathcal{P}ic_{A/k}$ is represented by a group scheme over
   $k$ whose identity component $A^\vee = \operatorname{Pic}^0_{A/k}$ is an abelian variety, the
   *dual* of $A$, with $\dim A^\vee = \dim A = \dim_k H^1(A, \mathcal{O}_A)$; its formation commutes
   with extension of the field. The restriction $P$ of the universal rigidified line bundle to $A
   \times A^\vee$, the *Poincaré bundle*, is universal: for every $k$-scheme $T$ and every line
   bundle $L$ on $A \times T$, rigidified along $\{0\} \times T$, whose restrictions to the fibres
   $A_{k(t)}$ over the points $t$ of $T$ lie in $\operatorname{Pic}^0$, there is a unique morphism
   $\alpha \colon T \to A^\vee$ with $(\mathrm{id} \times \alpha)^* P \cong L$ as rigidified line
   bundles. In particular $A^\vee(k) = \operatorname{Pic}^0(A)$.
2. For a line bundle $L$ on $A$, the Mumford bundle $m^* L \otimes p^* L^{-1} \otimes q^* L^{-1}$,
   as a family of line bundles on $A$ parametrized by $A$, defines a homomorphism $\varphi_L \colon
   A \to A^\vee$, given on points by $a \mapsto t_a^* L \otimes L^{-1}$. If $L$ is ample,
   $\varphi_L$ is an isogeny with kernel $K(L)$.
3. (Dual homomorphisms.) A homomorphism $f \colon A \to B$ of abelian varieties induces a
   homomorphism $f^\vee \colon B^\vee \to A^\vee$, the unique one with $(\mathrm{id} \times
   f^\vee)^* P_A \cong (f \times \mathrm{id})^* P_B$ as line bundles on $A \times B^\vee$ rigidified
   along $\{0\} \times B^\vee$. The map $f \mapsto f^\vee$ is additive and $(n_A)^\vee = n_{A^\vee}$
   for all $n \in \mathbb{Z}$; if $f$ is an isogeny, so is $f^\vee$, and there is a canonical
   isomorphism of group schemes $\operatorname{Ker}(f)^D \cong \operatorname{Ker}(f^\vee)$ with the
   Cartier dual of $\operatorname{Ker}(f)$. In particular $A^\vee[n]$ is canonically the Cartier
   dual of $A[n]$ for every $n \ge 1$.
4. (Biduality.) Rigidify $P$ also along $A \times \{0\}$, compatibly with the given rigidification
   at $(0, 0)$, and pull it back to $A^\vee \times A$ by the switch $s \colon A^\vee \times A \to A
   \times A^\vee$. As a family of line bundles on $A^\vee$ parametrized by $A$, $s^* P$ defines a
   homomorphism $\kappa_A \colon A \to A^{\vee\vee}$, and $\kappa_A$ is an isomorphism. Moreover
   $\varphi_L = \varphi_L^\vee \circ \kappa_A$ for every line bundle $L$ on $A$.

Hence a pair $(B, L)$ of an abelian variety $B$ and a line bundle $L$ on $A \times B$, rigidified
along $\{0\} \times B$, with restrictions to the fibres over the points of $B$ in
$\operatorname{Pic}^0$, is a dual of $A$, as a family of line bundles, exactly when the morphism $B
\to A^\vee$ that classifies $L$ is an isomorphism of schemes. For $B$ to be the dual as an abelian
variety, with its own group law, require also that $L|_{A \times \{0_B\}}$ be trivial: the
classifying isomorphism then sends $0_B$ to $0$ and is a homomorphism; pulling $P$ back by a nonzero
translation of $A^\vee$ gives a family that is still universal, but whose classifying isomorphism is
not a homomorphism. A test on points alone does not suffice: for an elliptic curve $E$ over
$\mathbb{C}$, $A = E \times E$, $B = E$ and $L$ the pull-back of the Poincaré bundle of $E$ by
$(\mathrm{pr}_1, \mathrm{id}) \colon A \times B \to E \times E^\vee$, with $E^\vee$ identified with
$E$, the restriction of $L$ to $A \times \{b\}$ is trivial only for $b = 0$, but $\dim B = 1 \ne 2 =
\dim A^\vee$; and in positive characteristic a morphism that is injective on points may have a
nontrivial infinitesimal kernel.

Van der Geer and Moonen take the representability of $\mathcal{P}ic_{A/k}$, with projective
connected components, from the general theory, and show that $\operatorname{Pic}^0_{A/k}$ is
reduced: for an ample $L$, $\varphi_L$ has the finite kernel $K(L)$, so $\dim
\operatorname{Pic}^0_{A/k} \ge \dim A$, while the dimension of the Picard scheme is at most $\dim_k
H^1(A, \mathcal{O}_A)$, with equality only if it is smooth, and $\dim_k H^1(A, \mathcal{O}_A) \le
\dim A$ for the abelian variety $A$. They deduce 3 from the universal property and their Proposition
(7.4), which describes the line bundles with trivial pull-back along the quotient $A \to A /
\operatorname{Ker}(f) = B$ by the characters of $\operatorname{Ker}(f)$, and 4 from $\varphi_L =
\varphi_L^\vee \circ \kappa_A$ and a comparison of degrees. Over an algebraically closed field Milne
constructs $A^\vee$ instead as the quotient of $A$ by $K(L)$, after Mumford's *Abelian Varieties*.

## Depends on

- [Abelian scheme](abelian-scheme.md), for abelian varieties over a field
- [Finite locally free group schemes and Cartier duality](deformations-and-p-divisible-groups/finite-locally-free-group-schemes-and-cartier-duality.md),
  for the Cartier dual of $\operatorname{Ker}(f)$ in 3

## Proof depends on

- [Representability of relative Picard functors](representability-of-picard-functors.md), for the
  Picard scheme of $A$, its tangent space and the bound $\dim_k H^1(A, \mathcal{O}_A) \le \dim A$
- [Theorem of the cube, theorem of the square and the seesaw principle](theorem-of-the-cube.md), for
  the Mumford bundle, $K(L)$ and its finiteness for ample $L$
- [Abelian varieties are projective](abelian-varieties-are-projective.md), for an ample line bundle
- [Isogenies of abelian schemes](isogenies-of-abelian-schemes.md), for the kernels of isogenies and
  their degrees
- [Finite locally free group schemes and Cartier duality](deformations-and-p-divisible-groups/finite-locally-free-group-schemes-and-cartier-duality.md),
  for its item 3 (van der Geer–Moonen, Proposition (7.4)), applied to the quotient of $A$ by
  $\operatorname{Ker}(f)$, from which van der Geer and Moonen deduce 3 (their Theorem (7.5))

## Sources

- G. van der Geer and B. Moonen, *Abelian Varieties*, book draft, Chapter VI, "The Picard scheme of
  an abelian variety", <https://www.math.ru.nl/personal/bmoonen/BookAV/DualAV1.pdf>: §3, the
  rigidified Picard functor, the Poincaré bundle and $\varphi_L$, Theorem (6.18) and Definition and
  Notation (6.19), pp. 95–96; and Chapter VII, "Duality",
  <https://www.math.ru.nl/personal/bmoonen/BookAV/DualAV2.pdf>: Proposition (7.4), Theorem (7.5),
  (7.7), Lemma (7.8), Theorem (7.9) and Corollary (7.17), pp. 99–104.
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, §8: Proposition 8.4 and the
  definition of $\operatorname{Pic}^0(A)$, the definition of the dual abelian variety and the
  Poincaré sheaf, Remark 8.7, and the construction of the dual over an algebraically closed field
  (referring to Mumford, p. 77, and, in positive characteristic, to Mumford's Chapter III).
- D. Robert, *Theory of abelian varieties and their moduli spaces*, draft book (version of 7 March
  2023), <https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/books/avtheory.pdf>:
  Corollary 2.3.5 and the rigidified Picard functor of §2.3.2, pp. 13–14.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the relative form of this result, over an arbitrary base, as
  `GlobalTheory.Published.DualAbelianScheme`.
