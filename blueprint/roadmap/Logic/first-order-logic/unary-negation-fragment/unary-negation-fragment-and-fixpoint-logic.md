# Unary negation fragment and unary negation fixpoint logic

The unary negation fragment UNFO is the fragment of first-order logic in which negation may be applied only to formulas with at most one free variable. Unary negation fixpoint logic UNFP extends it with least fixpoints of monadic predicates, without parameters.

**UNFO.** Over a relational schema, UNFO is given by the grammar

$$
\varphi ::= R(\bar{x}) \mid x = y \mid \varphi \wedge \varphi \mid \varphi \vee \varphi \mid \exists x\, \varphi \mid \neg\varphi(x),
$$

where in the last clause $\varphi$ has no free variable other than possibly $x$. In particular $x \neq y$ is not expressible. $\mathrm{UNFO}^{\neq}$ extends UNFO with inequalities $x \neq y$, and $\mathrm{UNFO}^{\neg}$ extends it with negated relational atoms $\neg R(\bar{x})$.

**UNFP.** Let $X, Y, \dots$ be extra unary predicates. UNFP is the extension of UNFO over the schema enlarged by these predicates with the least fixpoint construction

$$
[\mathrm{LFP}_{X,x}\, \varphi(X, \bar{X}, x)]\,(y),
$$

where $X$ occurs only positively in $\varphi$ and $\varphi$ has no free first-order variable other than $x$. Its semantics is that of least fixpoint logic: $y$ satisfies the formula when it belongs to the least fixpoint of the monotone map $A \mapsto \{a : \varphi(A, \bar{X}, a)\}$. In the extension with *non-monadic* fixpoints, the operator is $[\mathrm{LFP}_{X, \bar{x}}\, \varphi](\bar{y})$ with $X$ a relation variable of arity $|\bar{x}|$ occurring only positively in $\varphi$, and $\varphi$ with no free first-order variables other than $\bar{x}$.

A fragment of first-order logic is a *conservative reduction class* if there is a computable map from arbitrary first-order formulas to formulas of the fragment that preserves satisfiability and finite satisfiability.

## Depends on

None.

## Proof depends on

None.

## Expansion

UNFO generalizes modal logic and conjunctive queries, and UNFP generalizes the modal μ-calculus and monadic Datalog. UNFO has the finite model property; UNFP does not, but its finite satisfiability problem is decidable. Satisfiability is 2ExpTime-complete for both logics, on arbitrary and on finite structures.

## Sources

- B. ten Cate and L. Segoufin, "Unary negation", *Logical Methods in Computer Science* 9(3), paper 25, 2013, doi:[10.2168/LMCS-9(3:25)2013](https://doi.org/10.2168/LMCS-9(3:25)2013). Numbering of the version read, arXiv:1309.2069v2: Section 2.1 (the definitions of UNFO and UNFP), Section 1 (finite model property and complexity), and Section 7.3 (the extensions $\mathrm{UNFO}^{\neq}$ and $\mathrm{UNFO}^{\neg}$ and conservative reduction classes).
