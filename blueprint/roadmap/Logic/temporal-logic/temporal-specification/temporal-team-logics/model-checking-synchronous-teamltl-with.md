# Model checking synchronous TeamLTL with inclusion atoms and Boolean disjunction is undecidable

Under synchronous team semantics, model checking LTL extended with inclusion atoms and Boolean disjunction is Σ⁰₁-hard, and adding a single universal subteam quantifier makes it Σ¹₁-hard.

**Theorem (Virtema, Hofmann, Finkbeiner, Kontinen and Yang).** *Synchronous TeamLTL* evaluates LTL formulas in negation normal form on pairs $(T, i)$ of a set $T$ of traces and a position $i$: $p$ holds if $p \in t[i]$ for all $t \in T$, $\neg p$ if $p \notin t[i]$ for all $t \in T$, $\wedge$ is conjunction, $\varphi \vee \psi$ holds if $T = T_1 \cup T_2$ with $(T_1, i) \models \varphi$ and $(T_2, i) \models \psi$, and the temporal operators move all traces in lockstep ($\mathsf X\varphi$ holds at $(T, i)$ iff $\varphi$ holds at $(T, i+1)$, and similarly for $\mathsf U$ and $\mathsf W$). TeamLTL$(\subseteq, \varovee)$ adds *inclusion atoms* $\varphi_1 \cdots \varphi_n \subseteq \psi_1 \cdots \psi_n$ with propositional arguments, true at $(T, i)$ if every tuple of truth values taken by $(\varphi_1, \ldots, \varphi_n)$ on some trace at $i$ is also taken by $(\psi_1, \ldots, \psi_n)$ on some trace, and the *Boolean disjunction* $\varphi \varovee \psi$, true if $\varphi$ or $\psi$ holds at $(T, i)$; the *universal subteam quantifier* $\mathsf A\varphi$ holds if $\varphi$ holds at $(S, i)$ for every $S \subseteq T$. The *model-checking problem* asks, given a finite Kripke structure $K$ and a formula $\varphi$, whether $(\mathrm{Traces}(K), 0) \models \varphi$. Then:

1. model checking TeamLTL$(\subseteq, \varovee)$ is $\Sigma^0_1$-hard (Theorem 2 of the source);
2. model checking TeamLTL$(\subseteq, \varovee, \mathsf A)$ is $\Sigma^1_1$-hard, already for formulas with a single occurrence of $\mathsf A$ (Theorem 3);
3. the satisfiability problems of these two logics are $\Sigma^0_1$-hard and $\Sigma^1_1$-hard, respectively (Corollary 4), and it is undecidable whether a TeamLTL$(\subseteq, \varovee)$ formula is $1$-coherent, that is, holds at a team $(T, i)$ exactly when it holds at $(S, i)$ for every $S \subseteq T$ with $|S| \le 1$ (Definition 7, Theorem 12).

Here a set of natural numbers is $\Sigma^1_1$-hard if every set definable by a formula $\exists f\, \forall n\, R(f, n, x)$ of second-order arithmetic, with $f$ ranging over functions $\mathbb N \to \mathbb N$ and $R$ recursive, many-one reduces to it; such a set is not in the arithmetical hierarchy.

TeamLTL with Boolean negation is complete for third-order arithmetic (Lück), while model checking left-flat TeamLTL$(\varovee, \mathrm{A}^1)$ formulae, with Boolean disjunction and the singleton subteam quantifier, is in EXPSPACE, and in PSPACE in data complexity (Theorem 15); this logic is downward closed and expresses exactly the downward-closed generalized atoms, so atoms such as inclusion atoms are outside it.

## Depends on

- [Kripke structures with initial states](../kripke-structures-with-initial-states.md)
- [Formulas of linear temporal logic](../../linear-temporal-logic/formula.md)
- [The arithmetical class $\Sigma_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

*Part 1.* For a three-counter machine with instructions $I$ and a label $b$, a Kripke structure $K_I$ and a formula $\varphi_{I, b}$ are built so that $\mathrm{Traces}(K_I) \models \varphi_{I, b}$ iff the machine has a lossy computation that visits instruction $b$ infinitely often. A team $T$ encodes the configuration at step $j$ through $T[j, \infty]$: propositions $0, \ldots, n-1$ give the current instruction, and the value of counter $s$ is the number of distinct suffixes $t[j, \infty]$ with $c_s \in t[j]$; inclusion atoms and Boolean disjunctions enforce the transitions.

*Part 2.* The proof is analogous, for non-lossy computations: whether a nondeterministic three-counter machine has a computation visiting a given instruction infinitely often is $\Sigma^1_1$-complete, and a single universal subteam quantifier, in a formula stating that traces that differ once differ at every later position, rules out the losses. Both completeness facts for counter machines, $\Sigma^0_1$ for lossy and $\Sigma^1_1$ for non-lossy recurrence, are taken from the literature the source cites. A good expansion adds pages for the analytical hierarchy, its level $\Sigma^1_1$ and completeness under many-one reductions, which the statement uses, for the $\Sigma^0_1$-completeness of lossy recurrence and for the $\Sigma^1_1$-completeness of recurrence for nondeterministic three-counter machines.

## Sources

- J. Virtema, J. Hofmann, B. Finkbeiner, J. Kontinen and F. Yang, "Linear-Time Temporal Logic with Team Semantics: Expressivity and Complexity", in *41st IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2021)*, Leibniz International Proceedings in Informatics 213, Schloss Dagstuhl, 2021, paper 52, <https://doi.org/10.4230/LIPIcs.FSTTCS.2021.52>; numbers from arXiv:2010.03311v3, <https://arxiv.org/abs/2010.03311v3>: Section 2 (team semantics, inclusion atoms, Boolean disjunction, subteam quantifiers), Theorems 2 and 3, Corollary 4, Definition 7, Theorems 12 and 15 and the complexity table.
