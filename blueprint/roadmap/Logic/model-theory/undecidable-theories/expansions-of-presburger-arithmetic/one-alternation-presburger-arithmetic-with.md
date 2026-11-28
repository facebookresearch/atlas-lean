# The one-alternation fragment of Presburger arithmetic with divisibility is undecidable

The truth of sentences ∀x⃗ ∃y⃗ φ in Presburger arithmetic with divisibility over the integers is undecidable even when the existential variables may not occur on the left of a divisibility, and even when divisibility constraints may not be negated.

**Fragments.** *Presburger arithmetic with divisibility* (PAD) is the first-order theory of $\langle\mathbb Z,0,1,+,<,\mid\rangle$, where $a\mid b$ holds when $b=ac$ for some $c\in\mathbb Z$ (see [Presburger arithmetic](../../quantifier-elimination-for-presburger-arithmetic.md) for the divisibility-free part). Quantifier-free PAD formulas are Boolean combinations of atoms $f(\vec x)<g(\vec x)$ and $f(\vec x)\mid g(\vec x)$ with linear polynomials $f$, $g$ with integer coefficients. The fragment $\forall\exists_R\mathrm{PAD}$ consists of the sentences

$$
\forall x_1\cdots\forall x_n\,\exists y_1\cdots\exists y_m\;\varphi(\vec x,\vec y),
$$

with $\varphi$ quantifier-free, in which every divisibility atom has the form $f(\vec x)\mid g(\vec x,\vec y)$; that is, the existentially quantified variables do not occur on the left of a divisibility. The *positive* fragment $\forall\exists_R\mathrm{PAD}^+$ further requires $\varphi$ to be built with $\wedge$ and $\vee$ from divisibility atoms, order atoms and negated order atoms.

**Theorem (Bozga and Iosif; Pérez and Raha).** Truth of $\forall\exists_R\mathrm{PAD}$ sentences is undecidable (Bozga and Iosif; Proposition 3 of the source), and so is truth of $\forall\exists_R\mathrm{PAD}^+$ sentences (Pérez and Raha; Theorem 2).

The second statement corrects an earlier claim that the positive fragment is decidable, on which a decision procedure for parameter synthesis in one-counter automata had relied. Pérez and Raha identify a decidable restriction of $\forall\exists_R\mathrm{PAD}^+$ that still suffices to encode that synthesis problem, which is therefore decidable.

## Depends on

- [Quantifier elimination for Presburger arithmetic](../../quantifier-elimination-for-presburger-arithmetic.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Bozga and Iosif define in $\forall\exists_R\mathrm{PAD}$, through the complementary fragment, the least-common-multiple relation, then squaring and finally multiplication, so that solvability of Diophantine equations reduces to the fragment and the DPRM theorem applies. Lechner's translation computes, for every $\forall\exists_R\mathrm{PAD}$ sentence, an equivalent $\forall\exists_R\mathrm{PAD}^+$ sentence, which transfers undecidability to the positive fragment. A good expansion links pages for the Bozga–Iosif definition of multiplication (sketched in the paragraph before Proposition 3 of the source and carried out in the proof of Proposition 3 in Appendix B) and for Lechner's translation (Proposition 1).

## Sources

- G. A. Pérez and R. Raha, "Revisiting parameter synthesis for one-counter automata", in *30th EACSL Annual Conference on Computer Science Logic (CSL 2022)*, Leibniz International Proceedings in Informatics 216, pp. 33:1–33:18, 2022, doi:[10.4230/LIPIcs.CSL.2022.33](https://doi.org/10.4230/LIPIcs.CSL.2022.33); read in arXiv:2005.01071v6 ([arXiv](https://arxiv.org/abs/2005.01071v6)), whose numbering is used: the definitions of PAD, $\forall\exists_R\mathrm{PAD}$ and $\forall\exists_R\mathrm{PAD}^+$ in Section 2, Proposition 1 (Lechner's translation), Theorem 2 and Proposition 3 in Section 2.2, with the proof of Proposition 3 in Appendix B.
- M. Bozga and R. Iosif, "On decidability within the arithmetic of addition and divisibility", in *Foundations of Software Science and Computational Structures (FoSSaCS 2005)*, Lecture Notes in Computer Science 3441, pp. 425–439, 2005, doi:[10.1007/978-3-540-31982-5_27](https://doi.org/10.1007/978-3-540-31982-5_27), cited by the source for the undecidability of $\forall\exists_R\mathrm{PAD}$.
