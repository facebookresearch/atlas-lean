# Homomorphisms of abelian schemes and commutativity

Let $k$ be a field, $S$ a connected variety over $k$ (for instance $S = \operatorname{Spec} k$), and
$A$ and $B$ [abelian schemes](abelian-scheme.md) over $S$, with zero sections $e_A$ and $e_B$.

1. Every morphism $\alpha \colon A \to B$ of $S$-schemes with $\alpha \circ e_A = e_B$ is a
   homomorphism.
2. The group structure of $A$ is determined by its zero section: two laws of composition on the
   $S$-scheme $A$ that make it an abelian scheme with the same zero section coincide.
3. $A$ is commutative.

For $S = \operatorname{Spec} k$ these are Milne's Corollaries I.1.2 and I.1.4: every morphism
$\alpha \colon A \to B$ of abelian varieties over $k$ is a homomorphism followed by the translation by
the point $\alpha(0) \in B(k)$, and the group law of an abelian variety is commutative.

Milne deduces the first statement from the [rigidity lemma](rigidity-lemma.md), applied to the
morphism $(x, y) \mapsto \alpha(x + y) - \alpha(x) - \alpha(y)$ from $A \times_S A$ to $B$, which
sends the fibre over the zero section to the zero section; the second statement follows from the
first applied to the identity of $A$, and the third from the first applied to the inverse
$x \mapsto -x$, which is then a homomorphism.

## Depends on

- [Abelian scheme](abelian-scheme.md)

## Proof depends on

- [Rigidity lemma](rigidity-lemma.md)

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Corollary 16.2 (a)–(c) with its proof
  (families of abelian varieties over a variety), and Theorem 1.1, Corollary 1.2, Remark 1.3 and
  Corollary 1.4 (the case of a field).
