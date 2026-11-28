# Downward-closed sets of a preordered commutative monoid form a BI-algebra

For every Kripke resource monoid, a preordered commutative monoid whose operation is monotone, the downward-closed subsets form a BI-algebra under the operations read off from the resource semantics of BI; when the preorder is an equivalence relation, this BI-algebra is Boolean.

Let $(M, \circ, e, \sqsubseteq)$ be a [Kripke resource monoid](elementary-kripke-resource-models.md): a commutative monoid with a preorder $\sqsubseteq$ such that $m \sqsubseteq m'$ and $n \sqsubseteq n'$ imply $m \circ n \sqsubseteq m' \circ n'$. A set $X \subseteq M$ is *downward closed* if $n \sqsubseteq m$ and $m \in X$ imply $n \in X$. Let $D(M)$ be the set of downward-closed subsets of $M$, ordered by inclusion, with

$$
X \wedge Y = X \cap Y, \quad X \vee Y = X \cup Y, \quad \top = M, \quad \bot = \emptyset, \quad X \to Y = \{ m \mid \forall n \sqsubseteq m\ (n \in X \Rightarrow n \in Y) \},
$$

$$
\mathrm{I} = \{ m \mid m \sqsubseteq e \}, \quad X \ast Y = \{ m \mid \exists n, n' \in M\ (m \sqsubseteq n \circ n',\ n \in X,\ n' \in Y) \}, \quad X \mathrel{-\!\!\ast} Y = \{ m \mid \forall n \in M\ (n \in X \Rightarrow n \circ m \in Y) \}.
$$

Then each of these sets is downward closed and $(D(M), \subseteq, \wedge, \vee, \to, \top, \bot, \ast, \mathrm{I}, \mathrel{-\!\!\ast})$ is a [BI-algebra](bi-algebras.md). If $\sqsubseteq$ is an [equivalence relation](../../../Order/ordered-sets/equivalence-relation.md), then $D(M)$ is a Boolean BI-algebra, in which $X \to Y = (M \setminus X) \cup Y$.

## Depends on

- [BI-algebras](bi-algebras.md)
- [Elementary Kripke resource models](elementary-kripke-resource-models.md)
- [Equivalence relation](../../../Order/ordered-sets/equivalence-relation.md)

## Proof depends on

None.

## Expansion

The Heyting part is the standard algebra of downward-closed sets of a preorder (Kripke's semantics of intuitionistic logic read algebraically). For the multiplicative part: $X \ast Y$ is downward closed because $\sqsubseteq$ is transitive; $X \mathrel{-\!\!\ast} Y$ is downward closed because $m' \sqsubseteq m$ gives $n \circ m' \sqsubseteq n \circ m$ by monotonicity and $Y$ is downward closed; $\mathrm{I}$ is a unit because $m \sqsubseteq e \circ m$ and, for $n \sqsubseteq e$, $n \circ n' \sqsubseteq n'$; associativity and commutativity come from those of $\circ$ with monotonicity; and $Z \ast X \subseteq Y$ holds exactly when $Z \subseteq X \mathrel{-\!\!\ast} Y$. When $\sqsubseteq$ is an equivalence relation, downward-closed sets are unions of classes and are closed under complement. Under this algebra, the interpretation of a proposition is the set of worlds that force it in the elementary forcing semantics of Pym, O'Hearn and Yang, which orders worlds the opposite way to [elementary Kripke resource models](elementary-kripke-resource-models.md) (reversing $\sqsubseteq$ turns downward-closed sets into upward-closed ones and one convention into the other). Mathlib's `LowerSet` gives the lattice part, a complete and completely distributive lattice. Its multiplication of lower sets is the pointwise product $\{ n \circ n' \mid n \in X, n' \in Y \}$, defined only for ordered commutative groups; there the pointwise product of lower sets is already downward closed (if $m \sqsubseteq n \circ n'$ then $m = (m \circ n'^{-1}) \circ n'$ with $m \circ n'^{-1} \sqsubseteq n$), so it agrees with $X \ast Y$ above. The construction here is more general, applying to every preordered commutative monoid with a monotone operation, so the BI-algebra structure is a separate construction. This construction gives the predicates of a resource model a BI-algebra structure; the [separation algebras](../../../ComputerScience/program-logics-and-verification/separation-logic-metatheory/abstract-separation-logic/separation-algebras.md) of abstract separation logic give their predicates a similar structure with a partial operation and the discrete order.

## Sources

- D. J. Pym, P. W. O'Hearn and H. Yang, "Possible worlds and resources: the semantics of BI", *Theoretical Computer Science* 315(1) (2004), 257–305, <https://doi.org/10.1016/j.tcs.2003.11.020>; numbering from the author copy read (dated 29 November 2002), <https://www.cantab.net/users/david.pym/POY-resource-tcs.pdf>: Section 3.4 (the forcing clauses with the bifunctoriality condition, and the paragraph after Lemma 5 stating that the downwards-closed subsets of a preordered commutative monoid form a BI-algebra, Boolean when the preorder is an equivalence relation).
- Mathlib, files `Mathlib/Order/UpperLower/CompleteLattice.lean` (`LowerSet.completelyDistribLattice`) and `Mathlib/Algebra/Order/UpperLower.lean` (the multiplication of lower sets of an ordered commutative group, `IsLowerSet.mul_left` and `mul_lowerClosure`) at commit fc4f59e577feb1a4956671bc04ac18aaaf8cd842, <https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Order/UpperLower.lean>, for the comparison only.
