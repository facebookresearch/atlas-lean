# Extensions of two-variable or fluted logic with Craig interpolation are undecidable

Any abstract logic that extends two-variable first-order logic or the fluted fragment, has the Craig interpolation property, admits an effective translation of the base fragment and effective conjunction, and can express negation (or a weak form of quantification), has an undecidable satisfiability problem.

**Abstract logics.** An *abstract logic* $L$ assigns to each finite relational signature a set of formulas, each with finitely many free variables, and has a satisfaction relation between structures, assignments and formulas, subject to the reduct and renaming properties. $L$ *expresses* a formula $\psi$ of a logic $L'$ if some $\varphi \in L$ has the same free variables and signature and the same satisfying structures and assignments; $L'$ is an *extension* of $L$ ($L \preceq L'$) if $L'$ expresses all formulas of $L$. $L$ has the *Craig interpolation property* (CIP) if whenever $\varphi \models_L \psi$ there is $\vartheta \in L$ over the common signature, with free variables $\mathrm{free}(\varphi) \cap \mathrm{free}(\psi)$, such that $\varphi \models_L \vartheta \models_L \psi$. An *effective translation* from $L$ to $L'$ is a computable map sending each formula to an equivalent one; $L$ has *effective conjunction* if a formula equivalent to $\varphi \wedge \psi$ is computable from $\varphi$ and $\psi$. *Ordered quantification* means expressing $\exists x_n \varphi$ and $\forall x_n \varphi$ whenever $x_n$ is the free variable of $\varphi$ with the largest index.

**Theorem (ten Cate and Comer).** Let $L$ be an abstract logic with CIP and effective conjunction.

1. If $L$ extends the [fluted fragment](../guarded-and-fluted-fragments/fluted-fragment.md) $\mathrm{FL}$ and there is an effective translation from $\mathrm{FL}$ to $L$, then satisfiability for $L$ is undecidable provided $L$ can express ordered quantification or negation.
2. If $L$ extends [two-variable logic](../two-variable-logic-and-its-extensions/two-variable-logic-and-its-counting-extension.md) $\mathrm{FO}^2$ and there is an effective translation from $\mathrm{FO}^2$ to $L$, then satisfiability for $L$ is undecidable provided $L$ can express universal quantification or negation.

(Both are the two theorems of Section 6.) Earlier sections of the source show that forward logics with CIP, the natural extensions of the forward fragment, can express all of first-order logic; Section 6 extracts undecidability under much weaker expressive assumptions.

## Depends on

- [Fluted fragment](../guarded-and-fluted-fragments/fluted-fragment.md)
- [Two-variable logic and its counting extension](../two-variable-logic-and-its-extensions/two-variable-logic-and-its-counting-extension.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-variable fluted logic with three transitive relations is undecidable](../guarded-and-fluted-fragments/two-variable-fluted-logic-with-three-transitive.md)

## Expansion

Using CIP, the formulas $\psi_0(x_1) = \forall x_2 \forall x_3 (R(x_1,x_2) \wedge R(x_2,x_3) \to R(x_1,x_3))$ and $\psi_1 = \neg \forall x_1 \forall x_2 \forall x_3 (R(x_1,x_2) \wedge R(x_2,x_3) \to R(x_1,x_3))$ arise as unique interpolants of valid entailments between $\mathrm{FO}^2$ or $\mathrm{FL}$ formulas with auxiliary predicates, so $L$ expresses them. Ordered (or universal) quantification of $\psi_0$, or negation of $\psi_1$, then expresses transitivity of $R$, and by renaming, transitivity of several relations. Satisfiability is reduced from $\mathrm{FL}$ with three transitive relations (undecidable by Pratt-Hartmann and Tendera) in clause 1, and from $\mathrm{FO}^2$ with two transitive relations (undecidable by Kieroński) in clause 2, by conjoining the translated formula with the transitivity sentences.

## Sources

- Balder ten Cate and Jesse Comer, "Craig interpolation for decidable first-order fragments", *Logical Methods in Computer Science* 21(3):22, 2025, doi:10.46298/lmcs-21(3:22)2025; read as arXiv:2310.08689v6, <https://arxiv.org/abs/2310.08689v6>: Section 2 (abstract logics, CIP, expressibility and extensions), Section 5 (forward logics and ordered quantification) and Section 6 (the proposition on expressing transitivity and the two undecidability theorems for extensions of $\mathrm{FL}$ and $\mathrm{FO}^2$) of arXiv:2310.08689v6.
