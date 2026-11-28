# Non-termination of asynchronous programs with cancel is undecidable

There is no algorithm that decides whether an asynchronous program with cancel has an infinite run. The same holds for the existence of a fair infinite run and for fair starvation of a handler.

**Theorem.** It is undecidable, given an [asynchronous program with cancel](asynchronous-programs-with-cancel.md) $\mathcal{P}$, whether $\mathcal{P}$ has an infinite run from its initial configuration.

## Depends on

- [Asynchronous programs with cancel](asynchronous-programs-with-cancel.md)
- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof adapts Esparza, Finkel and Mayr's argument for broadcast protocols. From a two-counter machine $C$ and a set $F$ of control locations one builds a three-counter machine $C'$ that simulates $C$, increments the third counter after every step and returns to its initial configuration when $C$ reaches $F$; then $C'$ has an infinite bounded computation (counter sums below some bound) iff $C$ reaches $F$. An asynchronous program with cancel simulates $C'$ weakly: its main handler posts $b$ instances of a handler $I$, counter values are numbers of pending instances of handlers $c_1, c_2, c_3$, and the then-branch of a zero test is guessed by dispatching $I$ and canceling $c_j$. A wrong guess (a cheat) removes pending instances; the number of pending instances never exceeds $b$ and drops only at cheats, so an infinite run cheats finitely often and a cheat-free suffix is an infinite bounded computation of $C'$. Hence $\mathcal{P}$ has an infinite run iff $C$ reaches $F$. The same section sketches the modifications showing that fair non-termination and fair starvation are undecidable too.

A good expansion links pages for the three-counter construction whose infinite bounded computations witness reachability of $F$ (after Esparza, Finkel and Mayr), and for the weak simulation of such machines by asynchronous programs with cancel.

## Sources

- Pierre Ganty and Rupak Majumdar, "Algorithmic verification of asynchronous programs", *ACM Transactions on Programming Languages and Systems* 34(1), Article 6, 48 pages, 2012, <https://doi.org/10.1145/2160910.2160915>; read as arXiv:1011.0551v3, <https://arxiv.org/abs/1011.0551v3>: the theorem on infinite runs in Section 7.5 and its proof, and the subsequent theorem on fair infinite runs and fair starvation.
