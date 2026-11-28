# Inductive predicate synthesis modulo programs is undecidable

Inductive predicate synthesis modulo programs asks for implementations of unimplemented Boolean functions, such as representation invariants, under which a program with assertions becomes correct. Whether such implementations exist is undecidable over linear integer arithmetic; the reduction from two-counter machines uses programs with no unimplemented predicates.

**Setting (Wesley, Christakis, Navas, Trefler, Wüstholz and Gurfinkel).** Programs are written in an imperative language with integer variables, functions, assignments, conditionals, while loops and assertions, over a first-order signature $\Sigma$ and a finite variable set. A *partial predicate* of a program $\mathcal{P}$ is a pure Boolean function without an implementation; $\mathrm{Partial}(\mathcal{P})$ is the set of them, and $\mathcal{P}[\Pi]$ implements each $p \in \mathrm{Partial}(\mathcal{P})$ by returning the quantifier-free formula $\Pi(p)$ over its arguments. A program is *correct relative to a theory* $\mathcal{T}$ if its verification conditions, a system of constrained Horn clauses, have a $\mathcal{T}$-model; in particular a program with no partial predicates is correct only if no execution violates an assertion. An *IPS-MP problem* is a tuple $(\mathcal{P}, \mathcal{T}, \Pi_0)$ of a program, a theory and predicate templates $\Pi_0$; a *solution* is a map $\Pi$ from $\mathrm{Partial}(\mathcal{P})$ to quantifier-free formulas such that $\mathcal{P}[\Pi]$ is correct relative to $\mathcal{T}$ and $\Pi_0(p)$ implies $\Pi(p)$ in $\mathcal{T}$ for every $p$.

**Theorem (Wesley, Christakis, Navas, Trefler, Wüstholz and Gurfinkel).** For linear integer arithmetic, it is undecidable whether an IPS-MP problem has a solution.

The same paper reduces IPS-MP to constrained Horn clause solving and identifies a decidable case for programs over Boolean variables.

## Depends on

- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Proof sketch

The reduction is from the halting problem of two-counter machines. With variables $x, y$ for the counters and $z$ for the program counter, the program's main function first sets $x$ and $y$ to $0$ and $z$ to the first instruction, so that the run starts from the zero-counter configuration, and then runs a loop `while (true)` whose body dispatches on $z$: increments and decrements update a counter and advance $z$, a jump instruction sets $z$ according to whether a counter is $0$, and the halt instruction becomes `assert(false)`. The program has no partial predicates, so the IPS-MP problem has a solution exactly when the program is correct, that is, exactly when the machine does not halt from that configuration. The verification conditions quantify over all initial values (Definition 19 and Figure 8 of the source), so without this initialization a run could start at the halt instruction; the proof of Theorem 14 in the source omits it. The halting problem for two-counter machines started with both counters at $0$ is stated on the linked universality page.

## Sources

- Scott Wesley, Maria Christakis, Jorge A. Navas, Richard Trefler, Valentin Wüstholz and Arie Gurfinkel, "Inductive Predicate Synthesis Modulo Programs", 38th European Conference on Object-Oriented Programming (ECOOP 2024), LIPIcs 313, Article 43, 2024, <https://doi.org/10.4230/LIPIcs.ECOOP.2024.43>; the programming language and logical program verification of Section 3 ("Background"), Definition 4 in Section 4 ("IPS-MP: Problem Definition"), Theorem 14 in Section 5 ("Decidability of IPS-MP"), with Corollary 9 (Boolean programs) and Theorems 10 and 11 (the reduction to constrained Horn clauses), of the extended version arXiv:2407.08455v1, read at <https://arxiv.org/abs/2407.08455v1>.
