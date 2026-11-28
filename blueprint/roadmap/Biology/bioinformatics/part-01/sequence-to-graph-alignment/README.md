# Sequence-to-graph alignment

Pangenome references and assembly graphs represent sequence variation as a directed graph whose nodes carry letters, and reads must be aligned to paths in it. Exact matching and unit-cost semi-global alignment against such graphs generalize the Shift-And and Myers bit-vector algorithms from strings to graphs, including graphs with cycles, where the dynamic program has cyclic dependencies and scores must be iterated to convergence.

- [Sequence-to-graph alignment recurrence and the vertical property](sequence-to-graph-alignment-recurrence-and-vertical-property.md)
- [Convergence of priority-ordered bit-vector alignment on cyclic graphs](convergence-of-bitvector-alignment-on-cyclic-graphs.md)
