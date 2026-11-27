# Rigidity lemma

This node is still to be broken down: the statement is precise, but its proof, which the sources
give by reference to Mumford's *Geometric Invariant Theory*, is not.

Let $S$ be a connected noetherian scheme and $\pi \colon V \to S$ a proper flat morphism such that
$H^0(V_{\bar s}, \mathcal{O}_{V_{\bar s}}) = k(\bar s)$ for every geometric point $\bar s$ of $S$,
for instance one whose geometric fibres are nonempty, connected and reduced. Let $\pi' \colon V' \to
S$ be a separated $S$-scheme and $\alpha \colon V \to V'$ a morphism over $S$. If for some point $s$
of $S$ the image $\alpha(V_s)$ of the fibre $V_s$ in $V'_s$ is a single point, then $\alpha$ factors
through $\pi$: there is a morphism $\alpha' \colon S \to V'$ with $\alpha = \alpha' \circ \pi$.

In other words, if $\alpha$ is constant on one fibre of $\pi$, it is constant on every fibre. Milne
states the lemma for a connected base and fibres that are varieties, with his convention that
varieties are geometrically reduced and separated; the hypothesis on the fibres cannot be weakened
to geometric connectedness of integral fibres: over an imperfect field $k$, with $S =
\operatorname{Spec} k$ and $V = V' = \operatorname{Spec} L$ for a nontrivial finite purely
inseparable extension $L$, the identity has a one-point image but does not factor through $S$, which
has no morphism to $V'$. The lemma shows that
[morphisms of abelian schemes preserving the zero section are homomorphisms](homomorphisms-of-abelian-schemes.md).

## Depends on

- [Abelian scheme](abelian-scheme.md), for the conventions on varieties

## Proof depends on

- [Morphisms into the spectrum of an algebra](../schemes-and-morphisms/affine-group-schemes-and-hopf-algebras/morphisms-to-the-spectrum-of-an-algebra.md),
  for the case of an affine target over an affine open subscheme $\operatorname{Spec} R$ of $S$,
  where morphisms into $\operatorname{Spec} B$ over $\operatorname{Spec} R$ are the $R$-algebra maps
  from $B$ to global sections; these glue over $S$ to the correspondence of Robert, Remark 2.3.9,
  and the cohomological flatness of $\pi$ is a further input

## Expansion

A good expansion has pages for: the cohomological flatness of $\pi$ in dimension zero, that is,
$\mathcal{O}_{S'} \cong (\pi_{S'})_* \mathcal{O}_{V \times_S S'}$ for the base change $\pi_{S'}
\colon V \times_S S' \to S'$ of $\pi$ along every $S' \to S$, under the hypothesis on the fibres
(Robert, Lemma A.2.1); the case of an affine target, where $S$-morphisms $V \to V'$ correspond to
homomorphisms of unital quasi-coherent $\mathcal{O}_S$-algebras $\pi'_* \mathcal{O}_{V'} \to \pi_*
\mathcal{O}_V$, for $\pi' \colon V' \to S$ the structure morphism of $V'$ (Robert, Remark 2.3.9);
and Mumford's argument reducing the general case to an affine neighbourhood of the image of a fibre
(*Geometric Invariant Theory*, Proposition 6.1).

## Sources

- D. Robert, *Theory of abelian varieties and their moduli spaces*, draft book (version of 7 March
  2023), <https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/books/avtheory.pdf>: Lemma
  2.3.8 (rigidity lemma, with its hypotheses) and Remark 2.3.9, p. 15; Lemma A.2.1.
- J. S. Milne, "Abelian varieties", in *Arithmetic Geometry* (Storrs, 1984), Springer, 1986,
  103–150; revised version of 2 January 2022, <https://www.jmilne.org/math/xnotes/AVs.pdf>:
  Proposition 20.1 (rigidity lemma, over a connected scheme), p. 43.
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Proposition 16.1 (rigidity lemma),
  whose proof is a reference to Mumford below; the conventions of the preface. Theorem I.1.1 is the
  rigidity theorem for products of varieties over a field.
- D. Mumford, *Geometric Invariant Theory*, Ergebnisse der Mathematik 34, Springer, 1965:
  Proposition 6.1 (rigidity lemma), as cited by Milne and Robert.
