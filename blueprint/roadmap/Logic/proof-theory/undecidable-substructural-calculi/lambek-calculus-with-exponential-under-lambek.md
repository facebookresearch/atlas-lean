# The Lambek calculus with an exponential under Lambek's restriction is undecidable

The calculus EL⁻, which adds the linear-logic exponential to the product-free Lambek calculus while keeping Lambek's restriction to nonempty antecedents, has an undecidable derivability problem, already with right division only.

**Theorem (Kanovich, Kuznetsov and Scedrov).** Types are built from primitive types by the divisions $\backslash$ and $/$ and the modality $!$; a type not of the form $!B$ is a *non-bang-formula*. The sequent calculus $\mathbf{EL}^-$ derives sequents $\Pi \to A$ with nonempty antecedent $\Pi$ from the axioms $A \to A$ by the rules of the product-free Lambek calculus, in which the introduction rules $(\to \backslash)$ and $(\to /)$ require the remaining antecedent to contain a non-bang-formula, together with the rules for $!$: dereliction $\Delta_1, A, \Delta_2 \to B \,/\, \Delta_1, !A, \Delta_2 \to B$ when $\Delta_1, \Delta_2$ contain a non-bang-formula, weakening and contraction of $!A$ at the left end of the antecedent, and permutation of $!$-formulas with neighboring formulas; there is no rule introducing $!$ on the right. The derivability problem for $\mathbf{EL}^-$ is undecidable, and so is that of its fragment $\mathbf{EL}^-_/$ with right division only (Theorem 11 of the source). The same holds for the calculus $\mathbf{EL}_{mk}$ with marked types and for its right-division fragment (Theorem 12).

$\mathbf{EL}^-$ enjoys cut elimination (Theorem 2) and on sequents without $!$ derives exactly what the Lambek calculus with Lambek's restriction derives (Proposition 7), but admits substitution only for formulas without $!$. The source shows that no calculus with a reasonable exponential can have Lambek's restriction, cut elimination and substitution together (Theorems 3 and 4), and that the variant $\mathbf{EL}^*$ without Lambek's restriction is undecidable as well (Theorem 1).

## Depends on

- [Derivability in the Lambek calculus](../../../TheoryOfComputation/np-completeness/strings-and-puzzles/lambek-calculus-derivability/derivable.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces derivability in the Lambek calculus with right division extended by finite sets $\mathcal A$ of non-logical axioms of the forms $p, q \to r$ and $p / q \to r$, which is undecidable for a suitable $\mathcal A$ since grammars of this kind generate every recursively enumerable language (Buszkowski; Theorems 9 and 10). With $\Gamma_{\mathcal A}$ a list of the types $(r / q) / p$ for axioms $p, q \to r$ and $r / (p / q)$ for axioms $p / q \to r$, a sequent $\Pi \to A$ is derivable from $\mathcal A$ iff $!\Gamma_{\mathcal A}, \Pi \to A$ is derivable in $\mathbf{EL}^-_/$ (Lemma 9.1): the $!$-marked types can be copied, discarded and moved to wherever an axiom is used.

## Sources

- M. Kanovich, S. Kuznetsov and A. Scedrov, "Reconciling Lambek's restriction, cut-elimination and substitution in the presence of exponential modalities", *Journal of Logic and Computation* 30(1):239–256, 2020, <https://doi.org/10.1093/logcom/exaa010>; numbers from arXiv:1608.02254v2, <https://arxiv.org/abs/1608.02254v2>: Section 1 (Theorem 1, Lambek's restriction), Section 3 (the calculus $\mathbf{EL}^-$, Theorem 2), Theorems 3 and 4, Section 8 (Theorems 9 and 10) and Section 9 (Theorems 11 and 12, Lemma 9.1).
