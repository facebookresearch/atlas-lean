# ALC with visibly pushdown path expressions

The description logic ALC_vpl extends ALC with existential and universal restrictions along paths described by visibly pushdown languages over role names and tests, a decidable non-regular extension of propositional dynamic logic.

**Paths.** Fix concept names $N_C$, role names $N_R$ and individual names $N_I$, and let $\Sigma_{\mathrm{all}} = N_R \cup \{C? \mid C \in N_C\}$. For a language $L$ of finite words over a finite subset of $\Sigma_{\mathrm{all}}$ and an interpretation $\mathcal I$, a sequence $\rho = \rho_1 \cdots \rho_{n+1}$ of elements of $\Delta^{\mathcal I}$ is an *$L$-path* if there is a word $w_1 \cdots w_n \in L$ such that for each $i \le n$ either $w_i \in N_R$ and $(\rho_i, \rho_{i+1}) \in w_i^{\mathcal I}$, or $w_i = C?$ with $\rho_i = \rho_{i+1} \in C^{\mathcal I}$. The concept $\exists L.C$ denotes the set of elements from which an $L$-path leads to an element of $C^{\mathcal I}$, and $\forall L.C = \neg\exists L.\neg C$.

**Visibly pushdown languages.** A *pushdown alphabet* is an alphabet partitioned into call, internal and return letters. A *visibly pushdown automaton* is a pushdown automaton over a pushdown alphabet that pushes exactly one stack symbol on a call letter, leaves the stack unchanged on an internal letter, and pops one symbol (or reads the empty stack) on a return letter; a language is *visibly pushdown* if such an automaton accepts it. For call letter $r$ and return letter $s$, the language $r^\# s^\# = \{r^n s^n \mid n \in \mathbb N\}$ is visibly pushdown, and every regular language is.

**The logic.** The role names are partitioned into call, internal and return roles, and tests $C?$ are internal letters. $\mathcal{ALC}_{vpl}$ is ALC extended with the concepts $\exists L.C$ for visibly pushdown languages $L$ over finite subsets of this pushdown alphabet, given by nondeterministic visibly pushdown automata. Its extension with *nominals* $\{a\}$, interpreted as $\{a^{\mathcal I}\}$, is $\mathcal{ALCO}_{vpl}$, and its extension with the *Self* operator $\exists r.\mathsf{Self}$, interpreted as $\{d \mid (d, d) \in r^{\mathcal I}\}$, is $\mathcal{ALC}^{\mathsf{Self}}_{vpl}$. A concept $C$ is *satisfiable* if $C^{\mathcal I} \neq \emptyset$ for some interpretation $\mathcal I$.

## Depends on

- [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md)
- [PDL formulas](propositional-dynamic-logic-pdl/formula.md)
- [Visibly pushdown automata and visibly pushdown languages](../../../TheoryOfComputation/context-free-languages/visibly-pushdown-languages/visibly-pushdown-automata.md)

## Proof depends on

None.

## Expansion

Restricted to regular languages the logic is $\mathcal{ALC}_{reg}$, a notational variant of propositional dynamic logic, and $\mathcal{ALCO}_{reg}$ is PDL with nominals. Concept satisfiability for $\mathcal{ALC}_{vpl}$ is 2EXPTIME-complete (Löding, Lutz and Serre), and the logic generalizes many other decidable non-regular extensions of PDL.

## Sources

- B. Bednarczyk, "Exploring non-regular extensions of propositional dynamic logic with description-logics features", *Logical Methods in Computer Science* 20(2), paper 7, 2024, <https://doi.org/10.46298/lmcs-20(2:7)2024>; read as arXiv:2307.09913v5, <https://arxiv.org/abs/2307.09913v5>: Section 2 (ALC with extras, path expressions, visibly pushdown languages, the logic $\mathcal{ALC}_{vpl}$).
