# Decidability frontier for hybrid automaton reachability

This node collects the decidability boundary for rectangular hybrid automata as stated in its sources.

## Expansion

A sound expansion has separate pages for:

1. **Initialized rectangular automata** (Henzinger, Kopke, Puri and Varaiya): reachability, and emptiness of
   ω-languages under bounded nondeterminism, are PSPACE-complete (Theorem 3.18 and Corollary 3.28), by translation to timed
   automata.
2. **Uninitialized extensions:** reachability is undecidable already for timed automata with one stopwatch that is not
   reset when its rate changes (Theorem 4.1, slopes $1$ and $0$), and for the other generalizations of Section 4 of the source.
3. **Time-bounded reachability** (Brihaye et al.): reaching a target location within a fixed time bound is decidable for
   rectangular automata with nonnegative rates, initialized or not, which include stopwatch automata (Theorem 1); it is
   undecidable for rectangular automata with singular rates of both signs (Theorem 2) and for linear hybrid automata with
   singular, strictly positive, fixed-rate variables and diagonal constraints (Theorem 3).

Each class is stated with its exact guard, rate and nondeterminism restrictions; together the results are a comparison
of cited theorems, not a complete present-day classification.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Turing machine.
- Proof prerequisite: Timed automata region abstraction.

## Depends on

- [Rectangular and initialized rectangular automata](rectangular-and-initialized-rectangular-automata.md)

## Sources

- What's Decidable About Hybrid Automata? — T. A. Henzinger, P. W. Kopke, A. Puri, P. Varaiya, UC Berkeley Memorandum UCB/ERL M98/22 (preliminary version STOC 1995), Abstract; Sec. 1; Theorem 3.18, Corollary 3.28 and Theorem 4.1. <https://www2.eecs.berkeley.edu/Pubs/TechRpts//1998/ERL-98-22.pdf>
- On Reachability for Hybrid Automata over Bounded Time — T. Brihaye, L. Doyen, G. Geeraerts, J. Ouaknine, J.-F. Raskin, J. Worrell, ICALP 2011 (arXiv 1104.5335), Abstract; Theorems 1–3. <https://arxiv.org/html/1104.5335v1>
- EE 144/244 Fundamental Algorithms for System Modeling, Analysis, and Optimization (Fall 2015): Timed Automata — UC Berkeley EECS 144/244 lecture slides. <https://ptolemy.berkeley.edu/projects/embedded/eecsx44/lectures/Fall2015/wk12ta.pdf>
