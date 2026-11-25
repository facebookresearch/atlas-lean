# Decidable interface correctness criterion

Let a machine model and an interface (user) model be finite and [composed](user-model-and-machine-model-composition.md), with the error,
blocking and augmenting composite states defined there. Following Heymann and Degani, the interface is correct for the machine when no
composite state reachable from the initial composite state is an error, blocking or augmenting state. Correctness is decidable: given the
composite model explicitly, exploring its reachable part takes time linear in its numbers of states and transitions, and when the interface
is incorrect the exploration returns a path from the initial composite state to an offending state.

## Expansion

This node states a precise result. A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Algorithm cost model.

## Depends on

- [User model and machine model composition](user-model-and-machine-model-composition.md)

## Sources

- M. Heymann and A. Degani, *Constructing Human-Automation Interfaces: A Formal Approach*, HCI-Aero 2002, section "Formal Verification of Interfaces" (correctness as the absence of error, blocking and augmenting states in the composite model); the linear-time search is the standard graph search, which the source does not state. <https://cdn.aaai.org/HCI/2002/HCI02-019.pdf>
