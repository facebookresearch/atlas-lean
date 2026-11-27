# Homomorphisms of abelian schemes and commutativity

Let $S$ be a scheme and $A$ and $B$ [abelian schemes](abelian-scheme.md) over $S$, with zero sections
$e_A$ and $e_B$.

1. Every morphism $\alpha \colon A \to B$ of $S$-schemes with $\alpha \circ e_A = e_B$ is a
   homomorphism.
2. The group structure of $A$ is determined by its zero section: two laws of composition on the
   $S$-scheme $A$ that make it an abelian scheme with the same zero section coincide.
3. $A$ is commutative.

For $S = \operatorname{Spec} k$ these are Milne's Corollaries I.1.2 and I.1.4: every morphism
$\alpha \colon A \to B$ of abelian varieties over $k$ is a homomorphism followed by the translation by
the point $\alpha(0) \in B(k)$, and the group law of an abelian variety is commutative.

For $S$ connected and noetherian the first statement follows from the [rigidity
lemma](rigidity-lemma.md). Since the group law is not yet known to be commutative, write it
multiplicatively and consider the morphism over $A$, with $A \times_S A$ viewed over $A$ through the
second projection,

$$A \times_S A \to B \times_S A, \qquad (x, y) \mapsto \bigl(\alpha(xy)\, \alpha(y)^{-1} \alpha(x)^{-1},\ y\bigr).$$

The scheme $A$ is connected, and the fibres of the second projection are the fibres of $A$, which
satisfy the hypothesis of the rigidity lemma. Over the zero section $y = e_A$ the morphism sends
$(x, e_A)$ to $(e_B, e_A)$, so by the rigidity lemma it factors through a morphism $A \to B \times_S
A$, $y \mapsto (\beta(y), y)$; evaluating at $x = e_A$ gives $\beta(y) = e_B$, so $\alpha(xy) =
\alpha(x) \alpha(y)$.

Over an arbitrary $S$, let $\psi \colon A \times_S A \to B$ be the morphism $(x, y) \mapsto
\alpha(xy)\, \alpha(y)^{-1} \alpha(x)^{-1}$. On every geometric fibre, $\alpha$ is a morphism of
abelian varieties preserving zero, so by the noetherian case over the spectrum of the residue field
it is a homomorphism there, and $\psi$ maps the fibre to the zero of $B$. Let $s \in S$, let $S_0$
be an affine open neighbourhood of $s$ and $U \subset B_{S_0}$ an affine open subscheme containing
the zero of $B_s$. As $A \times_S A \to S$ is proper, the points of $S_0$ over which $\psi$ maps the
fibre of $A \times_S A$ into $U$ form an open neighbourhood of $s$; let $V$ be an affine open
neighbourhood of $s$ inside it. Then $\psi$ maps $(A \times_S A)_V$ into the affine $V$-scheme $U
\times_{S_0} V$, and as the push-forward of the structure sheaf of the abelian scheme $(A \times_S
A)_V$ is $\mathcal{O}_V$ (Robert, Lemma A.2.1), it factors through $V$; as $\psi(e_A, e_A) = e_B$,
$\psi$ is the zero section on $(A \times_S A)_V$. These $V$ cover $S$, so $\alpha(xy) = \alpha(x)
\alpha(y)$ over every $S$.

The second statement follows from the first applied to the identity of $A$, and the third from the
first applied to the inverse $x \mapsto x^{-1}$, which is then a homomorphism.

## Depends on

- [Abelian scheme](abelian-scheme.md)

## Proof depends on

- [Rigidity lemma](rigidity-lemma.md), for the noetherian case of 1, over a connected noetherian $S$
  and over the geometric points of a general $S$, and for the cohomological flatness $(\pi_V)_*
  \mathcal{O} = \mathcal{O}_V$ of an abelian scheme after every base change (Robert, Lemma A.2.1), a
  step of its proof plan, which the argument over an arbitrary base uses

## Sources

- J. S. Milne, "Abelian varieties", in *Arithmetic Geometry* (Storrs, 1984), Springer, 1986,
  103–150; revised version of 2 January 2022, <https://www.jmilne.org/math/xnotes/AVs.pdf>:
  Corollary 20.2 (a)–(c) with its proof, p. 43.
- D. Robert, *Theory of abelian varieties and their moduli spaces*, draft book (version of 7 March
  2023), <https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/books/avtheory.pdf>:
  Corollary 2.3.10 with its proof, p. 15, and Lemma A.2.1, p. 82 (the push-forward of the structure
  sheaf of an abelian scheme after base change).
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Corollary 16.2 (a)–(c) with its proof
  (families of abelian varieties over a variety), and Theorem 1.1, Corollary 1.2, Remark 1.3 and
  Corollary 1.4 (the case of a field).
