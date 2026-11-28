# Kripke completeness of finitely axiomatized normal modal logics is undecidable

There is no algorithm that decides, given a unimodal formula $\varphi$, whether the normal modal logic axiomatized over $\mathbf{K}$ by $\varphi$ is Kripke complete.

**Setting.** Formulas are [modal formulas](../kripke-semantics/formula.md) over a countably infinite set of atoms (the variables $p_0, p_1, \dots$ of the source). For a normal modal logic $L_0$, $\mathrm{NExt}\,L_0$ is the lattice of its normal extensions, and $L_0 \oplus \varphi$ is the least normal modal logic containing $L_0$ and $\varphi$, closed under modus ponens, uniform substitution and necessitation: the [theorems](../normal-modal-logics/derivable.md) of $\mathbf{K} \oplus \Lambda$ for $\Lambda$ the union of $L_0$ and the closure of $\{\varphi\}$ under [substitution](../kripke-semantics/subst.md); that page has no substitution rule, and $L_0$ is already closed under substitution. A logic is *Kripke complete* if it is the set of formulas valid in some class of Kripke frames; it has the *finite model property* if it is the set of formulas valid in some class of finite frames; it is *decidable* if membership in it is decidable. A property $P$ is *decidable in $\mathrm{NExt}\,L_0$* if some algorithm decides, for a formula $\varphi$ (a finite axiomatization, since finitely many axioms can be joined into one), whether $L_0 \oplus \varphi$ has $P$.

**Theorem (Thomason).** Kripke completeness is undecidable in $\mathrm{NExt}\,\mathbf{K}$: no algorithm decides, given a unimodal formula $\varphi$, whether $\mathbf{K} \oplus \varphi$ is Kripke complete.

As surveyed in the source, Kripke completeness, the finite model property and decidability are also undecidable in $\mathrm{NExt}\,\mathbf{K4}$ (where $\mathbf{K4} = \mathbf{K} \oplus \Box p \to \Box\Box p$), and the finite model property, decidability and tabularity are undecidable in $\mathrm{NExt}\,\mathbf{K}$ (Chagrov and coauthors; Kracht and Wolter). By contrast, consistency is decidable in $\mathrm{NExt}\,\mathbf{K}$, because this lattice has only two coatoms (Makinson), but it is undecidable for normal bimodal logics.

## Depends on

- [Theorems of a normal modal logic](../normal-modal-logics/derivable.md)
- [Substitution of a formula for an atom](../kripke-semantics/subst.md)
- [Kripke model](../kripke-semantics/kripke-model.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The source cites the result without proof. A good expansion gives Thomason's reduction and links the undecidable problem it starts from. Kracht and Wolter obtained the undecidability of decidability, the finite model property and tabularity in $\mathrm{NExt}\,\mathbf{K}$ through Thomason's simulation of polymodal logics by unimodal ones, and for transitive tense logics the analogous results are proved by reduction from reachability for Minsky machines.

## Sources

- S. K. Thomason, "Undecidability of the completeness problem of modal logic", in *Universal Algebra and Applications*, Banach Center Publications 9, PWN, 1982, pp. 341–345, doi:10.4064/-9-1-341-345 (original source, cited beside the copy read).
- Q. Chen and T. Takahashi, "Most properties are undecidable for transitive tense logics", *Electronic Proceedings in Theoretical Computer Science* 447, 2026, pp. 189–202, doi:10.4204/EPTCS.447.11; read as arXiv:2606.31863v1, <https://arxiv.org/abs/2606.31863v1>, whose numbering is used here: Section 1, the paragraph on $\mathrm{NExt}\,\mathbf{K}$ and Table 1, and Section 2 (decidability of properties in $\mathrm{NExt}\,L_0$).
