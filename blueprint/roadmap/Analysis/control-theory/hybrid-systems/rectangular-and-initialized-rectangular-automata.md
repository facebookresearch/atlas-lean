# Rectangular and initialized rectangular automata

A rectangular automaton is a hybrid automaton whose invariants, guards, initial sets and reset targets are rectangles
(products of intervals with rational or infinite endpoints) and whose flow condition in each location is a rectangular
differential inclusion $\dot x \in \prod_i [a_i, b_i]$. It is initialized if, on every edge along which the flow interval of a
variable changes, that variable is reset. Timed automata are the case in which every variable has rate exactly $1$ and jumps
are deterministic: every initial region is empty or a single point and every reset assigns a single rational value (in the
classical formulation, $0$). A stopwatch is a variable whose rate is fixed in each location to $0$ or to $1$; this is not the inclusion
$\dot x \in [0, 1]$, which allows rates varying in time.

## Depends on

- [Hybrid automata and their executions](hybrid-automata-and-their-executions.md)

## Sources

- What's Decidable About Hybrid Automata? — T. A. Henzinger, P. W. Kopke, A. Puri, P. Varaiya, UC Berkeley Memorandum UCB/ERL M98/22 (preliminary version STOC 1995), Sec. 2 (rectangular regions, rectangular automata, initialization) and Sec. 3.1 (finite-slope variables, deterministic jumps, timed automata, stopwatches). <https://www2.eecs.berkeley.edu/Pubs/TechRpts//1998/ERL-98-22.pdf>
