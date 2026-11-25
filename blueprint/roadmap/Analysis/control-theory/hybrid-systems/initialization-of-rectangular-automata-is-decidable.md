# Initialization of rectangular automata is decidable

Given a rectangular automaton with finitely many locations, edges and variables and rational data, it is decidable whether the
automaton is initialized: check, for every edge and every variable, whether the flow intervals of that variable in the source and
target locations are equal, and if they differ whether the edge resets the variable.

## Proof

Each test compares two pairs of rational or infinite endpoints and reads the edge's finite reset set; there are finitely many edges and
variables.

## Depends on

- [Rectangular and initialized rectangular automata](rectangular-and-initialized-rectangular-automata.md)

## Sources

- T. A. Henzinger, P. W. Kopke, A. Puri and P. Varaiya, *What's decidable about hybrid automata?*, UC Berkeley Memorandum UCB/ERL M98/22, Section 2 (initialization). <https://www2.eecs.berkeley.edu/Pubs/TechRpts//1998/ERL-98-22.pdf>
