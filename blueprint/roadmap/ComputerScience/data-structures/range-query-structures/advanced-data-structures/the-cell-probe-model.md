# The cell-probe model

In the *cell-probe model*, memory is a total map from the fixed set of cell addresses to $w$-bit words. A deterministic operation is a finite decision tree, chosen from the operation's input without inspecting the initial cell contents. Its execution returns the value at the reached leaf, the final memory, and the number of probes. The evaluation rules are:

- A return yields its value and leaves the memory unchanged, at zero probe cost.
- A read selects its continuation using the current word at the addressed cell and passes it unchanged memory.
- A write replaces only the addressed word before running its continuation, without observing the old word.

Each executed read or write adds one probe, including repeated accesses to the same cell and writes of the value already stored there. No other computation is charged. Addresses and word width are independent parameters: an address need not fit in a word. With no cells there are no addresses to probe; with zero-bit words each cell has only one possible value.

For comparison, a word-RAM instruction accesses only a bounded number of cells, so an operation taking $t$ word-RAM instructions uses $O(t)$ probes at the same word width. This is the basis for transferring lower bounds on probes to time in the [word RAM](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md), under the corresponding memory assumptions.

A data structure that stores addresses inside cells must choose a word wide enough to hold them.

## Background

- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- E. Demaine, *6.851: Advanced Data Structures*, Lecture 11 "Integer data structures" (scribe notes, Spring 2012, revised Fall 2017), MIT, <https://courses.csail.mit.edu/6.851/spring21/scribe/lec11.pdf>: Section 2 (the transdichotomous RAM, the word RAM, and the cell-probe model with $w$-bit cells, unit cost per read or write and free computation; the cell-probe model as the strongest of these models), and Section 3.3 (the cell-probe lower bound for predecessor with $n\,\mathrm{polylog}(n)$ space).
