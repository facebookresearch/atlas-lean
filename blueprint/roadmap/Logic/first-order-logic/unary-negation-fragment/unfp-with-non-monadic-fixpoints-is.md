# Unary negation fixpoint logic with non-monadic fixpoints is undecidable

Unary negation fixpoint logic is decidable with monadic fixpoints, but allowing fixpoint operators of higher arity makes satisfiability and finite satisfiability undecidable.

**Theorem (ten Cate and Segoufin).** The extension of [unary negation fixpoint logic](unary-negation-fragment-and-fixpoint-logic.md) UNFP with non-monadic least fixpoint operators has an undecidable satisfiability problem, both over arbitrary structures and over finite structures.

By contrast, satisfiability and finite satisfiability for UNFP itself are decidable and 2ExpTime-complete. The guarded fragment stays decidable even with guarded fixpoints of any arity.

## Depends on

- [Unary negation fragment and unary negation fixpoint logic](unary-negation-fragment-and-fixpoint-logic.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces containment of Datalog queries, which Shmueli showed undecidable on finite structures, by a proof that applies to every class of structures containing the encodings of finite strings. A Datalog query $\Pi_i$ is a negation-free formula $\varphi_{\Pi_i}$ of least fixpoint logic, so it lies in the extension of UNFP with non-monadic fixpoints. The containment of $\Pi_1$ in $\Pi_2$ holds exactly when

$$
\exists \bar{x}\, \bigl(\varphi_{\Pi_1}(\bar{x}) \wedge \textstyle\bigwedge_i P_i(x_i)\bigr) \wedge \neg\exists \bar{x}\, \bigl(\varphi_{\Pi_2}(\bar{x}) \wedge \textstyle\bigwedge_i P_i(x_i)\bigr)
$$

is unsatisfiable, with fresh monadic predicates $P_i$. Negation is applied only to sentences.

## Sources

- B. ten Cate and L. Segoufin, "Unary negation", *Logical Methods in Computer Science* 9(3), paper 25, 2013, doi:[10.2168/LMCS-9(3:25)2013](https://doi.org/10.2168/LMCS-9(3:25)2013). Numbering of the version read, arXiv:1309.2069v2: Theorem 7.2 and its proof in Section 7.3, and Section 1 (decidability of UNFP).
