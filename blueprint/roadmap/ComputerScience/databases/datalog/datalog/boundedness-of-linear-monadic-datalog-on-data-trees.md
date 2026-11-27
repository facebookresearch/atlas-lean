# Boundedness of linear monadic datalog on data trees is undecidable

On finite trees whose nodes carry labels from an infinite alphabet that can be compared for equality, it is undecidable whether a linear monadic datalog program using the child and descendant relations is equivalent to some nonrecursive program. Without the descendant relation the problem is decidable over words and ranked trees.

**Setting (Mazowiecki, Ochremiak and Witkowski).** Databases are finite words, or finite ranked or unranked trees, whose nodes carry labels from an infinite alphabet; programs can test a node for a fixed label and test whether two nodes carry equal labels. A datalog program is *monadic* if all intensional predicates in rule heads are unary, *linear* if every rule body uses at most one intensional predicate, and *connected* if within each rule all variables are connected; only connected monadic programs are considered. $\mathsf{Datalog}(\downarrow, \downarrow_+)$ allows the child relation $\downarrow$ and the descendant relation $\downarrow_+$ in rule bodies, $\mathsf{Datalog}(\downarrow)$ only the child relation, and $\mathsf{L\text{-}Datalog}(\downarrow, \downarrow_+)$ is the linear fragment of the former. A program is *bounded* if it is equivalent, over the considered class of databases, to a union of conjunctive queries (a nonrecursive program); the *boundedness problem* asks whether a given program is bounded.

**Theorem (Mazowiecki, Ochremiak and Witkowski).** The boundedness problem for $\mathsf{L\text{-}Datalog}(\downarrow, \downarrow_+)$ is undecidable over words and over ranked or unranked trees.

The same paper proves that containment of an $\mathsf{L\text{-}Datalog}(\downarrow, \downarrow_+)$ program in a union of conjunctive queries is undecidable over ranked and unranked trees, that boundedness for $\mathsf{Datalog}(\downarrow)$ is in PSPACE over words and in 2EXPTIME over ranked trees, and that containment of a linear $\mathsf{Datalog}(\downarrow)$ program in a union of conjunctive queries is EXPSPACE-complete over unranked trees.

## Depends on

- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The reduction asks whether a Turing machine has halting runs from the empty tape of arbitrary length, which is undecidable because a halting machine can be modified to idle arbitrarily long before halting. A tree encodes a run as a word of configurations separated by $\#$, each tape cell written as four consecutive nodes giving the row number, the next row number, the column number and the tape symbol, placed on a path from some node up to the root. The program is the disjunction of a recursive program $P$ that follows a correct encoding and a program $Q$, equivalent to a union of conjunctive queries, that detects errors in the encoding; on any tree with an error the combined program holds everywhere after three steps. The combined program is unbounded if and only if the machine has arbitrarily long halting runs.

## Sources

- Filip Mazowiecki, Joanna Ochremiak and Adam Witkowski, "Eliminating Recursion from Monadic Datalog Programs on Trees", Mathematical Foundations of Computer Science 2015 (MFCS 2015), Lecture Notes in Computer Science, pp. 394–406, 2015, <https://doi.org/10.1007/978-3-662-48057-1_31>; the boundedness undecidability theorem of Section 4 ("Boundedness") with its proof in the appendix section "Undecidability of the boundedness problem in general", the definitions in Sections 1 and 2, and the decidability results of Sections 3 and 4, of arXiv:1505.02444v1, read at <https://arxiv.org/abs/1505.02444v1>.
