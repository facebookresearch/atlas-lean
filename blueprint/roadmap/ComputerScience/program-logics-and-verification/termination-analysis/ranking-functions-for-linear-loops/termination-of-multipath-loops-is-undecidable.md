# Termination of multipath linear-constraint loops is undecidable

Whether a multipath linear-constraint loop terminates is undecidable over the integers, the rationals and the reals, both from every initial state and from a given one; this holds already for deterministic loops whose paths are mutually exclusive affine updates.

**Theorem.** For each domain $\mathbb D \in \{\mathbb Z, \mathbb Q, \mathbb R\}$, the following problems are undecidable for [multipath linear-constraint (MLC) loops](linear-constraint-loops.md), given by their rational guard and update matrices and vectors, whose variables range over $\mathbb D$ (for $\mathbb D = \mathbb R$ the transitions are the real points of the same polyhedra; the linked page defines the integer and rational cases):

1. *universal termination*: given the loop, is there no infinite execution from any initial state in $\mathbb D^n$?
2. *termination with initial states*: given the loop and a polyhedral set $S_0$ of initial states, given by rational linear inequalities, is there no infinite execution from any state of $S_0$?

Undecidability holds even for MLC loops in which every path is an affine single-path loop and the path guards are mutually exclusive, so that the loop is deterministic. The proof (Theorem 3.7 of the source) translates a counter program into an integer MLC loop with one variable per counter and a location variable, so that a single integer initial state suffices; over $\mathbb Q$ and $\mathbb R$ it uses Tiwari's observation that the generated loops terminate over $\mathbb Z$ iff they terminate over $\mathbb Q$ and over $\mathbb R$. Undecidability already holds with $3$ variables.

The source credits the observation to Tiwari (CAV 2004), building on the undecidability of mortality for piecewise affine systems of Blondel, Bournez, Koiran, Papadimitriou and Tsitsiklis (2001).

## Depends on

- [Linear-constraint loops](linear-constraint-loops.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The observation is due to Tiwari. A counter program with $n$ counters becomes an MLC loop with $n$ counter variables and a location variable $pc$: an increment or decrement of $x_i$ at location $j$ gives the path $\{pc = j,\ x_i' = x_i \pm 1,\ pc' = j + 1\}$, and a test "if $x_i > 0$ goto $k_1$ else goto $k_2$" at location $j$ gives the two paths $\{pc = j,\ x_i \ge 1,\ pc' = k_1\}$ and $\{pc = j,\ x_i \le 0,\ pc' = k_2\}$, with all other variables unchanged. Over $\mathbb Z$ this simulates the counter program exactly, so the halting problem gives undecidability with an initial state, and the undecidability of universal termination of counter programs (Blondel, Bournez, Koiran, Papadimitriou and Tsitsiklis, already for two counters) gives the universal case; with two counters the loop has $3$ variables. Over $\mathbb Q$ and $\mathbb R$ the generated loop terminates iff it terminates over $\mathbb Z$, which transfers both results. By contrast, termination of single-path affine loops is decidable over $\mathbb R$ and $\mathbb Q$ and, by later work, over $\mathbb Z$.

## Sources

- Amir M. Ben-Amram, Samir Genaim, Joël Ouaknine and James Worrell, "Termination Analysis of Linear-Constraint Programs", *Foundations and Trends in Programming Languages* 10(1–2), 2026, pp. 1–145, <https://doi.org/10.1108/FTPGL-07-2025-0071>; read as arXiv:2509.06752v3, <https://arxiv.org/abs/2509.06752v3>: Section 2.3 (Programs; universal termination and counter programs) and Theorem 3.7 in Section 3.3 ("Termination of Multi-path Linear-Constraint Loops") and Theorem 2.4 (universal termination of counter programs), in the numbering of that version.
