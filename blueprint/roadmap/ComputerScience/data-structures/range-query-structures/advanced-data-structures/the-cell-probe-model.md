# The cell-probe model

In the *cell-probe model*, a data structure's memory is an array of cells of $w$ bits each, where the word size $w$ is a parameter. The cost of an operation is the number of cells it reads or writes, its *probes*. All other computation is free, including arbitrary functions of the cells already read.

The model is stronger than the transdichotomous RAM and the [word RAM](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md). A word-RAM data structure with word size $w$ that uses $t$ time per operation makes at most $O(t)$ probes, since each word-RAM instruction touches $O(1)$ cells. So a lower bound on probes in the cell-probe model with word size $w$ is a lower bound on time for every word-RAM implementation with the same word size.

Usually $w = \Theta(\log n)$, or more generally $w \ge \log n$, so that a cell can hold a pointer.

## Background

- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- E. Demaine, *6.851: Advanced Data Structures*, Lecture 11 "Integer data structures" (scribe notes, Spring 2012, revised Fall 2017), MIT, <https://courses.csail.mit.edu/6.851/spring21/scribe/lec11.pdf>: Section 2 (the transdichotomous RAM, the word RAM, and the cell-probe model with $w$-bit cells, unit cost per read or write and free computation; the cell-probe model as the strongest of these models), and Section 3.3 (the cell-probe lower bound for predecessor with $n\,\mathrm{polylog}(n)$ space).
