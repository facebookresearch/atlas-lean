# BI is conservative over intuitionistic propositional logic

BI is a conservative extension of intuitionistic propositional logic: a judgement whose propositions use only additive connectives, with its hypotheses combined by ";", is provable in BI if and only if the corresponding sequent is provable in intuitionistic logic.

Call a BI proposition *additive* if it is built from propositional letters with $\top$, $\bot$, $\wedge$, $\vee$ and $\to$ only (no $\mathrm{I}$, $\ast$ or $\mathrel{-\!\!\ast}$). For all $n \ge 1$ and all additive propositions $\varphi_1, \dots, \varphi_n, \varphi$,

$$
\varphi_1 ; \dots ; \varphi_n \vdash \varphi \ \text{ is provable in BI} \iff \varphi_1, \dots, \varphi_n \vdash \varphi \ \text{ is provable in intuitionistic propositional logic}.
$$

On the left, provability is in the [natural deduction system NBI](natural-deduction-for-bi.md), and the hypotheses form an additive [bunch](formulas-and-bunches-of-bi.md) (associativity of ";" makes the bracketing irrelevant up to coherent equivalence). On the right, provability is in [natural deduction for intuitionistic propositional logic](../../propositional-logic/intuitionistic-propositional-logic/natural-deduction-for-intuitionistic-propositional-logic.md). O'Hearn and Pym's intuitionistic logic has the additive unit $1$ ($\top$); that calculus has none, so the page composes their Proposition 3(1) with the translation replacing every $\top$ by $\bot \to \bot$, which preserves and reflects intuitionistic provability. The right-hand side is the translated sequent.

Conservativity does not extend to multiplicative additive intuitionistic linear logic: BI proves the distribution of $\wedge$ over $\vee$, $\varphi \wedge (\psi \vee \chi) \vdash (\varphi \wedge \psi) \vee (\varphi \wedge \chi)$ and its converse, by the usual intuitionistic proof using ";" only.

## Depends on

- [Natural deduction for BI](natural-deduction-for-bi.md)
- [Natural deduction for intuitionistic propositional logic](../../propositional-logic/intuitionistic-propositional-logic/natural-deduction-for-intuitionistic-propositional-logic.md)

## Proof depends on

None.

## Expansion

Missing prerequisites of a proof page, for future pages:

- soundness and completeness of NBI for bicartesian doubly closed categories (O'Hearn and Pym's Proposition 4, with the published erratum that "DCC" there should read "bicartesian DCC");
- soundness and completeness of intuitionistic propositional logic for bicartesian closed categories, at the level of provability;
- or, for a syntactic proof instead: the equivalence of NBI and the sequent calculus LBI, together with [cut elimination for LBI](cut-elimination-for-lbi.md) and the subformula property of cut-free LBI derivations.

The direction from intuitionistic logic to BI translates each intuitionistic rule into the NBI rule of the same name over ";", with weakening and contraction of ";" supplying the shared contexts. For the converse, O'Hearn and Pym argue semantically: a bicartesian closed category, a model of intuitionistic proofs, is a bicartesian doubly closed category in which the two closed structures coincide, so on the additive fragment the denotations of BI proofs are exactly those of intuitionistic proofs. The companion statement that BI is conservative over multiplicative intuitionistic linear logic (their Proposition 3(2)) needs a page for that calculus first.

## Sources

- P. W. O'Hearn and D. J. Pym, "The logic of bunched implications", *The Bulletin of Symbolic Logic* 5(2) (1999), 215–244, <https://doi.org/10.2307/421090>, author copy read from the first author's publication page, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/BI.pdf> (numbering of the author copy; no page numbers cited): Section 2, Proposition 3(1) and the discussion of distribution after it, and Section 3, Proposition 4 and the paragraph on conservativity. Erratum to Proposition 4 as listed on the second author's BI page, <https://www.cantab.net/users/david.pym/BI.htm>.
