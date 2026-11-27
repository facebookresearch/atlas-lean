# Kripke semantics for intuitionistic propositional logic

This node covers Kripke semantics for intuitionistic propositional logic (IPC) over a type of atoms
with decidable equality, and the soundness and completeness theorem relating it to natural
deduction.

Formulas are built from atoms with $\wedge$, $\vee$ and $\to$ as primitive connectives and a
falsity $\bot$; $\neg\varphi$ abbreviates $\varphi \to \bot$. A Kripke model consists of a
nonempty set of nodes with a preorder $\le$ and a forcing relation between nodes and atoms that is
persistent: if $k \le k'$ and $k$ forces $p$, then $k'$ forces $p$. Forcing extends to all
formulas: no node forces $\bot$; $k$ forces $\varphi \wedge \psi$ when it forces both; $k$ forces
$\varphi \vee \psi$ when it forces at least one of them; and $k$ forces $\varphi \to \psi$ when
every $k' \ge k$ that forces $\varphi$ forces $\psi$. The main result: for a finite set $\Gamma$ of
formulas and a formula $\varphi$, $\varphi$ is derivable from $\Gamma$ in IPC exactly when, in
every Kripke model, every node that forces all members of $\Gamma$ forces $\varphi$.

## Expansion

A sound expansion has separate pages for:

1. the IPC derivation relation as the natural deduction relative to the intuitionistic axioms (all
   instances of ex falso $\bot \to B$), with $\bot$ a distinguished atom; if a Hilbert
   presentation is also used, the translations between the two presentations, preserving
   conclusions and hypotheses, are separate results;
2. Kripke models with persistent atoms, forcing in which the distinguished $\bot$ is never forced,
   and persistence of forcing for every formula;
3. soundness: derivability implies forcing;
4. completeness, by the canonical model of prime theories, or through Heyting algebras together
   with a proved representation of Heyting algebras by Kripke models (algebraic completeness alone
   is not Kripke completeness);
5. the equivalence of the preorder presentation with the partial-order presentation (by passing to
   the quotient by mutual accessibility), stated separately rather than assumed;
6. the finite-tree refinement, stated separately: for $\Gamma$ empty, the models may be restricted to
   finite trees with a root.

Minimal logic, without ex falso, is a different system with its own semantics. Completeness for
truth tables of the classical system does not cover this node.

## Sources

- J. Moschovakis, *Intuitionistic logic*, Stanford Encyclopedia of Philosophy, substantive revision 16 December 2022, §5.1. <https://plato.stanford.edu/entries/logic-intuitionistic/>
