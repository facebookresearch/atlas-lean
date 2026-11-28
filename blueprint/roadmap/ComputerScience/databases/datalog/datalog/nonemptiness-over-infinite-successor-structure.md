# Datalog nonemptiness over an infinite successor structure is undecidable

Over the fixed infinite structure consisting of a successor relation and a constant for its first element, no algorithm decides whether a given Datalog program derives at least one tuple for a given intensional predicate, in contrast with finite structures and all linear orders.

**Theorem.** Let $\mathcal B = (B, S^{\mathcal B}, N^{\mathcal B})$ be an infinite successor structure: $B$ is countably infinite with an enumeration $b_0, b_1, \dots$, $S^{\mathcal B} = \{(b_i, b_{i+1}) : i \ge 0\}$ and $N^{\mathcal B} = \{b_0\}$. Then the *Datalog nonemptiness problem over* $\mathcal B$ is undecidable: given a Datalog program $\Pi$ whose extensional symbols are among $S$ and $N$ and an intensional symbol $P$ of $\Pi$, it is undecidable whether the least fixed point $P_\infty^{\Pi, \mathcal B}$ computed by $\Pi$ on $\mathcal B$ is non-empty.

Here a Datalog rule is $P\bar x \leftarrow Q_1 \bar y_1, \dots, Q_m \bar y_m$ with relational atoms (0-ary symbols allowed and, unlike the safe rules usually required on finite databases, head variables not required to occur in the body), and $P_\infty^{\Pi, \mathcal B}$ is the value of $P$ in the least fixed point of the immediate-consequence operator of $\Pi$ over $\mathcal B$.

## Depends on

- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The source calls the proof a straightforward Turing machine simulation. If a Datalog program defines a successor structure inside a structure $\mathcal A$, a given transition function translates into Datalog rules that build the space-time diagram of a run, indexing time steps and tape cells by elements of the successor structure. Over $\mathcal B$ the successor structure is given directly and is infinite, so a designated intensional predicate becomes non-empty iff the machine halts on the empty input. On finite structures the problem is in EXPTIME, and the source's main theorem states that on every linear order, finite or infinite, it is decidable in EXPTIME and EXPTIME-complete as soon as the order has two elements.

## Sources

- Martin Grohe and Goetz Schwandtner, "The Complexity of Datalog on Linear Orders", *Logical Methods in Computer Science* 5(1), Paper 4, 2009, <https://doi.org/10.2168/LMCS-5(1:4)2009>; read in arXiv:0902.1179v2, <https://arxiv.org/abs/0902.1179v2>: Section 2 ("Preliminaries": Datalog and the nonemptiness problem), and the definition of successor structures and Proposition 4.3 in Section 4 ("Lower Bounds"), in the numbering of that version.
