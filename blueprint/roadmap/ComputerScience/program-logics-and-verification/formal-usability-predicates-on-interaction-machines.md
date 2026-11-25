# Formal usability predicates on interaction machines

This node collects usability predicates on a finite interaction machine (states, initial state, actions, transitions, display map), each
with its quantifiers fixed for nondeterministic machines.

## Expansion

A sound expansion has separate pages for:

1. **Graph predicates.** Every state is reachable from the initial state; the machine is strongly connected; there are no dead ends.
2. **Undo.** For every reachable state and action, there is an action sequence returning to the prior state; for nondeterministic
   machines, the page distinguishes the existence of such a path from a strategy that guarantees return against every resolution of
   nondeterminism.
3. **Observation predicates.** Predictability (states with equal displays have the same future observable behaviour, a bisimulation-style
   condition) and mode visibility (the mode is a function of the display).
4. **Decidability and implications.** Each predicate is decidable on finite machines; implications such as "undo for every action and
   reachability imply strong connectivity" (for deterministic machines) are separate lemmas.

## Depends on

- [Interactive device state machines](interactive-device-state-machines.md)

## Sources

- Formal methods in HCI (chapter) — Alan Dix (hcibook.com author page). <https://www.hcibook.com/alan/papers/formal-chapter-95/> Background reference.
- User Interface Design With Matrix Algebra — Harold Thimbleby, ACM TOCHI 2004 (CiteSeerX). <https://citeseerx.ist.psu.edu/document?doi=f5f87ecf5b9482b065e01f3eb0758ed7dfdd7882&repid=rep1&type=pdf> Background reference.
- Formal Verification of Medical Device User Interfaces Using PVS. <https://rd.springer.com/content/pdf/10.1007/978-3-642-54804-8_14.pdf> Background reference.
