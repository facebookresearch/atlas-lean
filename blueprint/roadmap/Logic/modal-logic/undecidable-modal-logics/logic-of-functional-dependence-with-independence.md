# The logic of functional dependence with independence atoms is undecidable

Adding independence atoms to the decidable logic of functional dependence produces an undecidable logic LFDI: no algorithm decides which LFDI formulas are valid in all dependence models.

**Theorem (Baltag and van Benthem).** The logic LFDI, the set of formulas of the [logic of functional dependence](logic-of-functional-dependence.md) extended with independence atoms $I_X y$ that are valid in all dependence models, is undecidable. Equivalently, satisfiability of LFDI formulas in dependence models is undecidable.

By contrast, LFD itself is decidable. The source also states that LFD becomes undecidable when extended with the Commutation axiom $\exists x \exists y\, \varphi \to \exists y \exists x\, \varphi$ (from Németi's undecidability of the corresponding CRS logic) or with the Stepwise axiom $\mathbb{E}_{X \cap Y}\varphi \to \mathbb{E}_X\mathbb{E}_Y\varphi$, where $\mathbb{E}$ is the dual of $\mathbb{D}$; these are separate statements.

## Depends on

- [Logic of functional dependence](logic-of-functional-dependence.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces satisfiability for the three-variable fragment of many-sorted first-order logic, whose undecidability the source recalls (from Henkin, Monk and Tarski). Formulas with variables $x, y, z$ are translated into LFD by replacing $\exists u\,\psi$ with $\mathbb{E}_{\{x, y, z\} \setminus \{u\}}\psi$. Independence atoms then force the admissible values of $x, y, z$ to form a full Cartesian product of their ranges, through $\mathbb{D}_\varnothing(I_x y \wedge I_{\{x, y\}} z)$; on such product models the translated quantifiers are the many-sorted first-order quantifiers, so a three-variable many-sorted formula is satisfiable iff its translation conjoined with this formula is.

## Sources

- A. Baltag and J. van Benthem, "A simple logic of functional dependence", *Journal of Philosophical Logic* 50(5):939–1005, 2021, doi:10.1007/s10992-020-09588-z; read as arXiv:2103.14946v1, <https://arxiv.org/abs/2103.14946v1>: Theorem 6.10 of arXiv:2103.14946v1 and its proof, with Facts 5.14 and 5.16.
