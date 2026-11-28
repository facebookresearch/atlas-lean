# Satisfiability and validity of ε-logic over finite models are Σ⁰₁- and Π⁰₁-complete

In ε-logic, first-order logic read over models with a probability measure in which ∀x means "for a set of x of measure at least 1 − ε", satisfiability in finite models and validity over finite models are as hard as in ordinary first-order logic for rational ε strictly between 0 and 1.

**ε-logic.** Fix $\epsilon\in[0,1]$ and a countable first-order language $\mathcal L$, possibly with equality. An *$\epsilon$-model* is a classical $\mathcal L$-structure $\mathcal M$ with a probability measure $\mathcal D$ on its domain (subject to measurability conditions). Formulas have the usual first-order syntax and are evaluated as follows: atomic formulas, $\wedge$, $\vee$ and $\exists$ are interpreted classically, while

$$
(\mathcal M,\mathcal D)\models\forall x\,\phi(x)\iff\Pr_{a\sim\mathcal D}\bigl[(\mathcal M,\mathcal D)\models\phi(a)\bigr]\ge1-\epsilon,
$$

and negation is pushed inward, with $\neg\forall x\,\phi$ read as $\exists x\,\neg\phi$ and $\neg\exists x\,\phi$ as $\forall x\,\neg\phi$. A sentence is *finitely $\epsilon$-satisfiable* if it holds in some $\epsilon$-model with finite domain, and *finitely $\epsilon$-valid* if it holds in all of them; *countable* satisfiability and validity are defined with countable domains. For $\epsilon=0$ the universal quantifier means "for almost all $x$".

**Theorem (Yang).**

1. Let $\mathcal L$ have infinitely many unary and at least three binary predicate symbols. For every rational $\epsilon\in(0,1)$, finite $\epsilon$-satisfiability of $\mathcal L$-sentences is $\Sigma^0_1$-complete (Theorem 3.4.4 and Corollary 3.4.9).
2. Let $\mathcal L$ have infinitely many unary and at least one binary predicate symbol. For every rational $\epsilon\in(0,1)$, finite $\epsilon$-validity is $\Pi^0_1$-complete (Theorem 3.5.9).
3. In any language with at least one binary relation symbol, finite $0$-validity is $\Pi^0_1$-complete (Corollary 3.5.3), and countable $0$-validity is $\Sigma^0_1$-complete (Corollary 3.5.4).
4. Under the assumptions of part 2, countable $\epsilon$-validity is $\Sigma^0_1$-hard for rational $\epsilon\in(0,1)$ (Corollary 3.5.10).

So Trakhtenbrot's theorem carries over to $\epsilon$-logic for $\epsilon>0$; by contrast, finite $0$-satisfiability is decidable, and all these problems are decidable for monadic relational languages. Without the restriction to finite models, Kuyper and Terwijn showed that general $\epsilon$-satisfiability is $\Sigma^1_1$-complete for rational $\epsilon\in(0,1)$.

## Depends on

- [Probability measure](../../../Probability/foundations/probability-measures/is-probability-measure.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Co-recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [The arithmetical class $\Sigma_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [The arithmetical class $\Pi_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [Validity of first-order sentences is undecidable](../../../TheoryOfComputation/undecidable-problems/validity-of-first-order-sentences-is-undecidable.md)
- [Satisfiability of relational calculus queries is undecidable](../../../ComputerScience/databases/query-language-expressiveness/satisfiability-of-relational-calculus-queries-is-undecidable.md)

## Expansion

Membership in $\Sigma^0_1$ (respectively $\Pi^0_1$) holds because finite $\epsilon$-models can be enumerated: a satisfying finite model with a rational measure can be searched for, and a failure of validity is witnessed by a finite model. Hardness of finite satisfiability (part 1) reduces the halting problem for Turing machines on the empty input, along the lines of the proof of Trakhtenbrot's theorem, through translations that force the probabilistic universal quantifier to behave classically on the relevant part of the model, using the additional unary predicates and the binary relations to control the measure; part 2 combines this with part 3. For $\epsilon=0$ the finitely valid sentences are exactly the classically finitely valid ones and the countably valid sentences are exactly the classically valid ones, so part 3 follows from Trakhtenbrot's theorem and from the undecidability of first-order validity. Trakhtenbrot's theorem, used in parts 1 and 3, is stated in its database form on [satisfiability of relational calculus queries is undecidable](../../../ComputerScience/databases/query-language-expressiveness/satisfiability-of-relational-calculus-queries-is-undecidable.md): satisfiability over finite instances is recursively enumerable but not recursive.

## Sources

- G. Yang, "Computability of validity and satisfiability in probability logics over finite and countable models", *Journal of Applied Non-Classical Logics* 25(4), pp. 324–372, 2015, doi:[10.1080/11663081.2016.1139967](https://doi.org/10.1080/11663081.2016.1139967); read in arXiv:1410.3059v2 ([arXiv](https://arxiv.org/abs/1410.3059v2)), titled "Computabilities of validity and satisfiability in probability logics over finite and countable models", whose numbering is used: Definitions 2.1.1 to 2.1.6 (ε-truth, ε-logic, ε-models, ε-validity and ε-satisfiability) and Definitions 2.3.1 and 2.3.5 (finite and countable models, satisfiability and validity), Theorem 3.4.4, Corollary 3.4.9, Corollaries 3.5.3 and 3.5.4, Theorem 3.5.9 and Corollary 3.5.10, and the summary tables of the introduction.
