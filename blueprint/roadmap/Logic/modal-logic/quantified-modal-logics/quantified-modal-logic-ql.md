# Quantified modal logic $\mathbf{Q}L$

For a propositional normal modal logic $L$, the quantified modal logic $\mathbf{Q}L$ is the least set of first-order modal formulas containing classical predicate logic and the axioms of $L$ and closed under predicate substitution, modus ponens, generalization and necessitation. Its formulas are interpreted in Kripke models with expanding domains.

**Language.** Countably many individual variables, countably many predicate letters of every arity, the connectives $\wedge$ and $\neg$, the modal box $\Box$ and the quantifier $\forall$ (with $\vee$, $\to$, $\exists$, $\Diamond$ defined as usual). There are no constants, no function symbols and no equality.

**Logics.** If $L$ is a propositional normal modal logic, $\mathbf{Q}L = \mathbf{QCl} \oplus L$, where $\mathbf{QCl}$ is classical predicate logic and $\oplus$ is closure under predicate substitution, modus ponens, generalization and necessitation. In particular $\mathbf{QK}$, $\mathbf{QT}$, $\mathbf{QD}$, $\mathbf{QK4}$, $\mathbf{QS4}$, $\mathbf{QKB}$, $\mathbf{QKTB}$, $\mathbf{QGL}$ and $\mathbf{QGrz}$ are the quantified counterparts of the corresponding propositional logics. A closed formula $\varphi$ is *$L$-satisfiable* when $\neg\varphi \notin L$.

**Semantics.** A predicate Kripke frame is $\langle W, R, D\rangle$ with $\langle W, R\rangle$ a Kripke frame and $D$ assigning to each world a nonempty domain so that $w R w'$ entails $D(w) \subseteq D(w')$ (expanding domains); it has *constant domains* when $w R w'$ entails $D(w) = D(w')$. A model adds an interpretation $I(w, P) \subseteq D(w)^n$ for each world and $n$-ary letter $P$. Under an assignment $g$, $\Box\varphi$ is true at $w$ iff $\varphi$ is true at every $w'$ with $w R w'$, and $\forall x\,\varphi$ is true at $w$ iff $\varphi$ is true for every $x$-variant $g'$ of $g$ with $g'(x) \in D(w)$. A formula is true in a frame when it is true at every world of every model on every predicate frame over it.

$\mathbf{QGL}$ and $\mathbf{QGrz}$ are Kripke incomplete; they are contained in the logics $\mathbf{QGL}^{sem}$ and $\mathbf{QGrz}^{sem}$ of all formulas true in every frame for $\mathbf{GL}$ (irreflexive, transitive, no infinite ascending chains) and $\mathbf{Grz}$ (the reflexive closures of such relations). $\mathbf{QKTB}$ is complete for reflexive symmetric frames.

## Depends on

- [Kripke model](../kripke-semantics/kripke-model.md)
- [Theorems of a normal modal logic](../normal-modal-logics/derivable.md)
- [Modal formulas](../kripke-semantics/formula.md)

## Proof depends on

None.

## Expansion

For a fixed sublanguage, such as formulas with at most two individual variables and a single monadic predicate letter, "$L$ is undecidable in that language" means that membership in $L$ of formulas of the sublanguage is undecidable.

## Sources

- M. Rybakov and D. Shkatov, "Undecidability of first-order modal and intuitionistic logics with two variables and one monadic predicate letter", *Studia Logica* 107(4):695–717, 2019, doi:10.1007/s11225-018-9815-7; read as arXiv:1706.05060v5, <https://arxiv.org/abs/1706.05060v5>: Section 2.1 (syntax, predicate frames and models, $\mathbf{Q}L$, $\mathbf{QGL}^{sem}$, $\mathbf{QGrz}^{sem}$ and $L$-satisfiability).
