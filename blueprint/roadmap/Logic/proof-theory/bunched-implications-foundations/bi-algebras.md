# BI-algebras

A BI-algebra is defined as a Heyting algebra equipped with an additional residuated commutative monoid structure on the same order; a Boolean BI-algebra is one whose Heyting part is a Boolean algebra. BI propositions are interpreted in BI-algebras connective by connective.

A *BI-algebra* is a structure $(A, \le, \wedge, \vee, \to, \top, \bot, \ast, \mathrm{I}, \mathrel{-\!\!\ast})$ such that

1. $(A, \le, \wedge, \vee, \to, \top, \bot)$ is a [Heyting algebra](../../propositional-logic/intuitionistic-propositional-logic/heyting-algebra-semantics-of-ipc.md): a lattice with greatest element $\top$ and least element $\bot$ in which $c \wedge a \le b$ exactly when $c \le a \to b$, for all $a, b, c \in A$;
2. $(A, \ast, \mathrm{I})$ is a commutative monoid whose operation is monotone, $a \le a'$ and $b \le b'$ giving $a \ast b \le a' \ast b'$;
3. $\ast$ is residuated with residual $\mathrel{-\!\!\ast}$ for the same order: $c \ast a \le b$ exactly when $c \le a \mathrel{-\!\!\ast} b$, for all $a, b, c \in A$.

The unit $\mathrm{I}$ need not be $\top$ and $\ast$ need not be $\wedge$. A *Boolean BI-algebra* is a BI-algebra whose Heyting algebra is a [Boolean algebra](../../../Order/lattices-boolean-algebras/boolean-algebra.md), with complement $a' = a \to \bot$; equivalently, $a \vee (a \to \bot) = \top$ for all $a$.

An *interpretation* in a BI-algebra $A$ assigns an element $[\![p]\!]_A$ to each propositional letter and extends to all [BI propositions](formulas-and-bunches-of-bi.md) by sending each connective to the operation of the same name: $[\![\varphi \ast \psi]\!]_A = [\![\varphi]\!]_A \ast [\![\psi]\!]_A$, $[\![\varphi \mathrel{-\!\!\ast} \psi]\!]_A = [\![\varphi]\!]_A \mathrel{-\!\!\ast} [\![\psi]\!]_A$, $[\![\mathrm{I}]\!]_A = \mathrm{I}$, and likewise for $\top, \bot, \wedge, \vee, \to$. One writes $\varphi \models \psi$ when $[\![\varphi]\!]_A \le [\![\psi]\!]_A$ for every BI-algebra $A$ and every interpretation in $A$.

## Depends on

- [Heyting algebra semantics of intuitionistic propositional logic](../../propositional-logic/intuitionistic-propositional-logic/heyting-algebra-semantics-of-ipc.md)
- [Boolean algebra](../../../Order/lattices-boolean-algebras/boolean-algebra.md)
- [Formulas and bunches of BI](formulas-and-bunches-of-bi.md)

## Proof depends on

None.

## Expansion

No prerequisite is missing. Residuation (3) already implies the monotonicity in (2) and that $a \ast (\cdot)$ preserves all joins that exist, in particular $a \ast (b \vee c) = (a \ast b) \vee (a \ast c)$ and $a \ast \bot = \bot$. The additive reduct of every BI-algebra is a Heyting algebra, complete or not, as Mathlib's `HeytingAlgebra` describes. A BI-algebra need not be a complete lattice, and only then do the complete-lattice classes apply: a BI-algebra whose lattice is complete is a commutative unital quantale in the sense of Mathlib's `IsQuantale` (the multiplication distributes over arbitrary suprema), with $a \mathrel{-\!\!\ast} b$ equal to Mathlib's residuation `leftMulResiduation a b` $= \sup \{ z \mid z \ast a \le b \}$, and its lattice is then a frame (`Order.Frame`). A general BI-algebra, with only finite joins guaranteed, is covered by `HeytingAlgebra` but not by those quantale and frame classes. The definition is a collapsed form of the bicartesian doubly closed categories that model BI proofs: one order carries two residuated structures.

## Sources

- D. J. Pym, P. W. O'Hearn and H. Yang, "Possible worlds and resources: the semantics of BI", *Theoretical Computer Science* 315(1) (2004), 257–305, <https://doi.org/10.1016/j.tcs.2003.11.020>; numbering from the author copy read (dated 29 November 2002), <https://www.cantab.net/users/david.pym/POY-resource-tcs.pdf>: Section 3.1 (the residuation laws for $\wedge, \to$ and for $\ast, \mathrel{-\!\!\ast}$, the definition of BI-algebra, interpretations and $\varphi \models \psi$) and Section 3.1 after Theorem 4 (Boolean BI-algebras).
- Mathlib, file `Mathlib/Algebra/Order/Quantale.lean` (`IsQuantale`, `leftMulResiduation`) at commit fc4f59e577feb1a4956671bc04ac18aaaf8cd842, <https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Algebra/Order/Quantale.lean>, for the comparison only.
