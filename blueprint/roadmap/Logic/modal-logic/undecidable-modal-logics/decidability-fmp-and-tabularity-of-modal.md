# Decidability, the finite model property and tabularity of finitely axiomatized modal logics are undecidable

There is no algorithm that decides, for a modal formula $\varphi$, whether the normal modal logic axiomatized over $\mathbf{K}$ by $\varphi$ is decidable, whether it has the finite model property, or whether it is tabular.

**Setting.** For [modal formulas](../kripke-semantics/formula.md) over [Kripke models](../kripke-semantics/kripke-model.md): $\mathrm{NExt}\,\mathbf{K}$ is the lattice of normal extensions of $\mathbf{K}$, $\mathbf{K} \oplus \varphi$ is the least normal modal logic containing $\varphi$, closed under modus ponens, uniform substitution and necessitation (the [theorems](../normal-modal-logics/derivable.md) of $\mathbf{K} \oplus \Lambda$ for $\Lambda$ the closure of $\{\varphi\}$ under [substitution](../kripke-semantics/subst.md); that page has no substitution rule), and a property is decidable in $\mathrm{NExt}\,\mathbf{K}$ if some algorithm decides, given $\varphi$, whether $\mathbf{K} \oplus \varphi$ has it. A logic has the *finite model property* if it is the set of formulas valid in some class of finite frames, is *decidable* if membership in it is decidable, and is *tabular* if it is the logic of a single finite frame.

**Theorem (Kracht and Wolter).** In $\mathrm{NExt}\,\mathbf{K}$, each of the following properties is undecidable: decidability, the finite model property, and tabularity.

Chagrov and his coauthors proved these and further properties undecidable in $\mathrm{NExt}\,\mathbf{K}$ by a different method, and Kracht and Wolter's results were obtained independently. Consistency, by contrast, is decidable in $\mathrm{NExt}\,\mathbf{K}$.

## Depends on

- [Modal formulas](../kripke-semantics/formula.md)
- [Kripke model](../kripke-semantics/kripke-model.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Theorems of a normal modal logic](../normal-modal-logics/derivable.md)
- [Substitution of a formula for an atom](../kripke-semantics/subst.md)
## Proof depends on

None.

## Expansion

Kripke completeness of finitely axiomatized normal modal logics is [undecidable as well](kripke-completeness-of-finitely-axiomatized.md).

The proof goes through the Thomason simulation, which embeds polymodal, in particular bimodal, logics into unimodal ones while preserving properties such as decidability, the finite model property and tabularity; undecidability of these properties for bimodal logics then transfers to $\mathrm{NExt}\,\mathbf{K}$. The copy read cites the result without proof; a good expansion links the simulation and the bimodal undecidability results.

## Sources

- M. Kracht and F. Wolter, "Normal monomodal logics can simulate all others", *Journal of Symbolic Logic* 64(1):99–138, 1999, doi:10.2307/2586754 (original source, cited beside the copy read).
- Q. Chen and T. Takahashi, "Most properties are undecidable for transitive tense logics", *Electronic Proceedings in Theoretical Computer Science* 447, 2026, pp. 189–202, doi:10.4204/EPTCS.447.11; read as arXiv:2606.31863v1, <https://arxiv.org/abs/2606.31863v1>: Section 1, the paragraph on $\mathrm{NExt}\,\mathbf{K}$ and Table 1.
