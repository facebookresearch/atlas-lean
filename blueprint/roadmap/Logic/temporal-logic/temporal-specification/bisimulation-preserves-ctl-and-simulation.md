# Bisimulation preserves CTL* and simulation preserves ACTL*

Let $M_1$, $M_2$ be Kripke structures over the same atomic propositions whose transition relations are total. If $R$ is a bisimulation between them that relates only states with the same labels, then $(s_1, s_2) \in R$ implies that $s_1$ and $s_2$ satisfy the same CTL* state formulas. If $R$ is a simulation of $M_1$ by $M_2$ relating only equally labelled states, then $(s_1, s_2) \in R$ implies that every ACTL* formula (CTL* with negations only on atoms and only universal path quantifiers) true at $s_2$ is true at $s_1$.

## Depends on

- [State formulas of CTL$^{\ast}$](../ctl/ctl-state-and-path-formulas/state-formula.md)

## Sources

- E. M. Clarke, O. Grumberg and D. A. Peled, *Model Checking*, MIT Press, 1999
- C. Baier and J.-P. Katoen, *Principles of Model Checking*, MIT Press, 2008, Sections 7.2 and 7.4
- J.-P. Katoen, *Model Checking*, Lecture 15: Bisimulation quotienting, RWTH Aachen University, 2019, "Simulation equivalence, ∀CTL* and ∀CTL", <https://moves.rwth-aachen.de/wp-content/uploads/WS1920/MC/mc2019_handout_lec15.pdf>
