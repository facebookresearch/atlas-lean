# Feasibility of control improvisation is undecidable

A control improvisation problem asks for a random generator of words accepted by an automaton that are admissible with high probability while no word is too likely. Deciding whether such a generator exists is undecidable when the automaton or the admissibility predicate is a probabilistic finite automaton, and in general for arbitrary computable predicates.

**Setting (Fremont, Donzé, Seshia and Wessel).** A *control improvisation instance* $\mathcal{C} = (\mathcal{I}, \alpha, \epsilon, \rho)$ consists of an *improvisation automaton* $\mathcal{I}$ over a finite alphabet $\Sigma$ (a DFA, an NFA or a [probabilistic finite automaton](../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/probabilistic-automata-and-cut-point-languages.md) with a cut-point), a computable *admissibility predicate* $\alpha : \Sigma^* \to \{0, 1\}$, a rational error probability $\epsilon \in [0, 1]$ and a rational probability bound $\rho \in (0, 1]$. Let $I = L(\mathcal{I})$ be the set of *improvisations* and $A = \{ w \in I : \alpha(w) = 1 \}$ the set of admissible ones. A distribution $D$ on $\Sigma^*$ is *$(\epsilon, \rho)$-improvising* if its support lies in $I$, $D(w) \le \rho$ for every $w$, and a word drawn from $D$ lies in $A$ with probability at least $1 - \epsilon$; $\mathcal{C}$ is *feasible* if such a distribution exists. Let $\mathcal{P}_1$ be the class of instances in which $\mathcal{I}$ is a probabilistic finite automaton and $\alpha$ is given by a DFA, and $\mathcal{P}_2$ the class in which $\mathcal{I}$ is a DFA and $\alpha$ is given by a probabilistic finite automaton.

**Theorem (Fremont, Donzé, Seshia and Wessel).**

1. For instances whose $\alpha$ is given by a Turing machine that halts on every input, there is a procedure that, given such an instance, halts exactly when the instance is feasible, and no procedure decides feasibility for all such instances (Corollaries 3.3 and 3.4 of the source).
2. For each of the classes $\mathcal{P}_1$ and $\mathcal{P}_2$, determining whether an instance is feasible is undecidable.

Read literally, Corollary 3.4 says that the set of feasible instances is computably enumerable; this holds only in the promise form of clause 1. The following is a remark of this page, not stated in the source: the set of feasible instances whose $\alpha$ is given by a machine $M$ halting on every input is not computably enumerable. With $\mathcal{T}$ the DFA accepting $\Sigma^*$, the instance $(\mathcal{T}, M, 1, 1)$ is feasible by Theorem 3.1 exactly when $M$ is such a machine, and the machines that halt on every input do not form a computably enumerable set.

Feasibility holds exactly when $|I| \ge 1/\rho$ and $|A| \ge (1 - \epsilon)/\rho$. When both components are given by DFAs, the same paper gives a polynomial-time improvisation scheme.

## Depends on

- [Probabilistic automata and cut-point languages](../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/probabilistic-automata-and-cut-point-languages.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../../../TheoryOfComputation/regular-languages/automata-and-expressions/weighted-automata-and-rational-series/emptiness-problem-for-probabilistic-automata.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

By the characterization of feasibility through the sizes of $I$ and $A$, the instance $(\mathcal{A}', \mathcal{T}, 0, 1/N)$, with $\mathcal{T}$ the trivial DFA accepting $\Sigma^*$, is feasible exactly when $|L(\mathcal{A}')| \ge N$. For clause 2, given a probabilistic automaton $\mathcal{A}$ with a cut-point, add deterministic states so that exactly $N$ words lead to the initial state of $\mathcal{A}$ and every other word is rejected; then $|L(\mathcal{A}')| \ge N$ exactly when $L(\mathcal{A})$ is nonempty, which is undecidable. For clause 1, given an instance whose $\alpha$ is total, both sets $I$ and $A$ are computably enumerable, so enumerating them until the sizes required by the characterization are reached halts exactly on feasible instances (Corollary 3.3), while for arbitrary computable $\alpha$ the condition $|A| \ge (1 - \epsilon)/\rho$ cannot be decided (Corollary 3.4). A good expansion links a page for the characterization of feasibility by the sizes of $I$ and $A$.

## Sources

- Daniel J. Fremont, Alexandre Donzé, Sanjit A. Seshia and David Wessel, *Control Improvisation*, 35th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2015), LIPIcs 45, 2015, pp. 463–474, https://doi.org/10.4230/LIPIcs.FSTTCS.2015.463; the definitions of control improvisation and feasibility, the feasibility theorem with its corollaries, and the undecidability theorem for probabilistic automata with its proof in the appendix, read in arXiv:1411.0698v5. Locators in arXiv:1411.0698v5: Theorem 3.1, Corollaries 3.3 and 3.4 and Theorem 5.3.
