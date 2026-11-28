# Two-variable logic and the guarded fragment with percentage quantifiers are undecidable

Finite satisfiability becomes undecidable when two-variable first-order logic is extended with the single quantifier "exactly half of the elements satisfy", and when the guarded fragment with three variables is extended with local percentage quantifiers over successors.

**Theorem (Bednarczyk, Orłowska, Pacanowska and Tan).** For a finite structure $\mathfrak M$ and a rational $q$ with $0 \le q \le 100$, the *global percentage quantifier* is interpreted by $\mathfrak M, y/a \models \exists^{=q\%} x\,\varphi(x, y)$ iff the number of $b \in M$ with $\mathfrak M \models \varphi(b, a)$ equals $\frac{q}{100}|M|$; for a binary relation $R$, the *local percentage quantifier* is interpreted by $\mathfrak M, x/a \models \exists^{=q\%}_R y\,\varphi(x, y)$ iff the number of $b$ with $R(a, b) \wedge \varphi(a, b)$ equals $\frac{q}{100}$ times the number of $b$ with $R(a, b)$. Let $\mathrm{FO}^2_{\mathrm{gl}\%}$ be the two-variable fragment of first-order logic with global percentage quantifiers, and $\mathrm{GF}_{\mathrm{loc}\%}$ the guarded fragment extended by local percentage quantifiers. Then:

1. finite satisfiability of $\mathrm{FO}^2_{\mathrm{gl}\%}$ is undecidable, even when the only percentage quantifier allowed is $\exists^{=50\%}$ (Theorem 6 of the source), and the same holds for two-variable logic with local percentage quantifiers (Corollary 7);
2. finite satisfiability of $\mathrm{GF}_{\mathrm{loc}\%}$ is undecidable, already for its three-variable fragment $\mathrm{GF}^3_{\mathrm{loc}\%}$ (Theorem 9).

By contrast, finite satisfiability is decidable for $\mathrm{GF}^2_{\mathrm{pres}}$, the two-variable guarded fragment with local Presburger quantifiers, which subsume local percentage quantifiers (Theorem 10), as it is for two-variable logic with counting quantifiers. The results strengthen earlier undecidability proofs for the description logic $\mathcal{ALCISCC}^{++}$ and for two-variable logic with the Härtig quantifier.

## Depends on

- [Two-variable logic and its counting extension](two-variable-logic-and-its-counting-extension.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

*Part 1.* The proof reduces a simpler form of Hilbert's tenth problem: given a system of equations $u = 1$, $u = v + w$ and $u = v \cdot w$ over pairwise distinct variables, is there a solution in $\mathbb N$ (Definition 2)? Each variable becomes a unary predicate whose number of elements is its value. If exactly half of the elements satisfy $\mathit{Half}$, $R$ implies $\mathit{Half}$ and $J$ implies $\neg\mathit{Half}$, then $\exists^{=50\%} x\,((\mathit{Half}(x) \wedge \neg R(x)) \vee J(x))$ expresses $|R| = |J|$; equicardinality, together with backward-functional binary relations expressible in this way, encodes addition and multiplication of cardinalities. Replacing $\exists^{=50\%} x$ by a local quantifier along a relation forced to be universal gives the local version.

*Part 2.* By reduction from the three-variable guarded fragment with a functional relation, which is undecidable, it suffices to express functionality of a relation with local percentage quantifiers, using the same equicardinality trick.

## Sources

- B. Bednarczyk, M. Orłowska, A. Pacanowska and T. Tan, "On Classical Decidable Logics Extended with Percentage Quantifiers and Arithmetics", in *41st IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2021)*, Leibniz International Proceedings in Informatics 213, Schloss Dagstuhl, 2021, paper 36, <https://doi.org/10.4230/LIPIcs.FSTTCS.2021.36>; numbers from arXiv:2106.15250v2, <https://arxiv.org/abs/2106.15250v2>: Section 2 (percentage quantifiers, the logics), Section 3 (Definition 2, the equicardinality trick, Theorem 6 and Corollary 7), Theorems 9 and 10, and Section 1.
