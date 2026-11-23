# Néron model of an abelian variety

Let $R$ be a discrete valuation ring with fraction field $K$ and residue field $k$, and let $A$ be an
[abelian variety](abelian-scheme.md) over $K$. The functor on smooth $R$-schemes

$$S \longmapsto \operatorname{Hom}_K(S \times_{\operatorname{Spec} R} \operatorname{Spec} K,\ A)$$

is represented by a smooth group scheme $\mathcal{A}$ over $R$, the **Néron model** of $A$ (Néron);
Bosch, Lütkebohmert and Raynaud include in the definition of a Néron model that it is separated and of
finite type over $R$. Thus $\mathcal{A}_K = A$, and every morphism from the generic fibre of a smooth
$R$-scheme $S$ to $A$ extends uniquely to an $R$-morphism $S \to \mathcal{A}$ (the Néron mapping
property); by the Yoneda lemma $\mathcal{A}$ is unique up to unique isomorphism. Its special fibre is
the smooth algebraic group $\mathcal{A}_k = \mathcal{A} \times_R k$ over $k$, and $A$ has **good
reduction** if $\mathcal{A}_k$ is an abelian variety.

This node is still to be broken down: the statement is precise, but its proof and the reduction
theory built on it are not. A good expansion follows Bosch, Lütkebohmert and Raynaud and has pages for:

- the definition of Néron models and their basic properties (BLR, chapter "What Is a Néron Model?",
  pp. 6–30), and Néron's existence theorem for abelian varieties with its construction (BLR, the
  chapters between those two);
- the properties of Néron models used by the reduction theorems: compatibility with étale base change,
  completion and henselization, and the behaviour of the identity component under finite extensions
  of $K$ (BLR, chapter "Properties of Néron Models", pp. 172–198; Conrad, §4, discussion before and
  after Theorem 4.4 and Corollary 4.5);
- the ingredients of the proof of the
  [semistable reduction theorem](semistable-reduction-theorem.md): its reduction to Jacobians of
  smooth proper geometrically connected curves (Conrad, Proposition 4.3), the semistable reduction
  theorem for curves, and Raynaud's description of the Néron model of a Jacobian through the Picard
  functor, with the open immersion criterion of Conrad's Theorem 4.4;
- the ingredients of the proof of the
  [potential good reduction of abelian varieties with complex multiplication](good-reduction-of-cm-abelian-varieties.md),
  following Serre and Tate: the Néron–Ogg–Shafarevich criterion for abelian varieties (good reduction
  if and only if inertia acts trivially on a Tate module $T_\ell A$, $\ell$ prime to the residue
  characteristic; Milne, Theorem IV.3.5, over number fields), its form for potential good reduction,
  and the action of inertia on the Tate module of an abelian variety with complex multiplication.

## Depends on

- [Abelian scheme](abelian-scheme.md), for abelian varieties and abelian schemes

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, §17: Theorem 17.1 and Remark 17.2
  (Néron's representability theorem, uniqueness by the Yoneda lemma, the special fibre, good
  reduction), with the notes at the end of §17 recommending Bosch–Lütkebohmert–Raynaud; Chapter IV,
  Theorem 3.5 (Néron–Ogg–Shafarevich criterion over number fields) and its proof.
- S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, Ergebnisse der Mathematik (3) 21,
  Springer, 1990: the chapters "What Is a Néron Model?" (pp. 6–30) and "Properties of Néron Models"
  (pp. 172–198).
- B. Conrad, "Semistable reduction for abelian varieties", seminar notes, Stanford, 2011,
  <http://math.stanford.edu/~conrad/mordellsem/Notes/L13.pdf>: §4 (Proposition 4.3, Theorem 4.4,
  Corollary 4.5 and the discussion of base change of Néron models).
- J.-P. Serre and J. Tate, "Good reduction of abelian varieties", Ann. of Math. (2) 88 (1968),
  492–517.
