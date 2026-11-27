# User model and machine model composition

Following Degani and Heymann, a machine model is a finite automaton over events with a mode label on each state, and an interface (user)
model is an automaton over the displayed modes and the events the user can trigger or observe. Events are classified as shared, which
synchronize the two models, or private to the machine; the composite model runs the two synchronously on shared events and the machine
alone on private ones. A composite state is an error state if the user model's displayed mode differs from the machine's mode; a blocking
state if the machine can take a shared event that the user model does not allow; and an augmenting state if the user model allows a shared
event that the machine cannot take. These predicates make precise the informal error, blocking and augmenting states of the cited source.

## Depends on

- [Interactive device state machines](interactive-device-state-machines.md)

## Sources

- Constructing Human-Automation Interfaces: A Formal Approach — Heymann and Degani, HCI-Aero 2002 (AAAI digital library), p. 121, section "Formal Verification Of Interfaces" (error, blocking and augmenting states of the composite model). <https://cdn.aaai.org/HCI/2002/HCI02-019.pdf>
