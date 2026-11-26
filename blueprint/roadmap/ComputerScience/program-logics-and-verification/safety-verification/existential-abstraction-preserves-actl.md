# Existential abstraction preserves ACTL*

Let $M = (S, I, R, L)$ be a Kripke structure, $AP_\varphi$ the set of atomic propositions used by a specification, and $h : S \to \hat S$ a surjection that respects them: $h(s) = h(t)$ implies $L(s) \cap AP_\varphi = L(t) \cap AP_\varphi$. The existential abstraction $\hat M$ has initial states $h(I)$, a transition $\hat s \to \hat t$ whenever $s \to t$ in $M$ for some $s \in h^{-1}(\hat s)$, $t \in h^{-1}(\hat t)$, and the labelling $\hat L(h(s)) = L(s) \cap AP_\varphi$. Then $\hat M$ simulates the restriction of $M$ to the labels $L(s) \cap AP_\varphi$, so every ACTL* formula over those propositions true in $\hat M$ is true in $M$. Predicate abstraction is the case in which $h$ maps a state to the truth values of a finite set of predicates. Without the respect hypothesis the transfer fails.

## Proof depends on

- [Bisimulation preserves CTL* and simulation preserves ACTL*](../../../Logic/temporal-logic/temporal-specification/bisimulation-preserves-ctl-and-simulation.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Generic labelled Kripke structure carrier (statement prerequisite)

## Sources

- E. Clarke, O. Grumberg, S. Jha, Y. Lu and H. Veith, "Counterexample-guided abstraction refinement", *CAV 2000*, LNCS 1855, Springer, 2000, Section 2 (existential abstraction and the respect condition) and Theorem 1, <http://www.cs.cmu.edu/afs/cs.cmu.edu/user/emc/www/papers/Conference%20Papers/Counterexample-guided%20Abstraction%20Refinement.pdf>
- E. M. Clarke, O. Grumberg and D. A. Peled, *Model Checking*, MIT Press, 1999
- J.-P. Katoen, *Model Checking*, Lecture 15: Bisimulation quotienting, RWTH Aachen University, 2019, "Simulation equivalence, ∀CTL* and ∀CTL", <https://moves.rwth-aachen.de/wp-content/uploads/WS1920/MC/mc2019_handout_lec15.pdf>
