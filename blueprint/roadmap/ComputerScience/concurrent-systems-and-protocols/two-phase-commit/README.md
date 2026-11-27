# Two-phase commit

- [Coordinator states](coord-state.md)
- [Participant states in two-phase commit](part-state.md)
- [Global states of two-phase commit](state.md)
- [Two-phase commit actions](action.md)
- [Updating one participant's state](set-part.md)
- [Transitions of two-phase commit](step.md)
- [Two-phase commit as a transition system](lts.md)
- [Initial state of two-phase commit](initial.md)
- [Reachable states of two-phase commit](reachable.md)
- [Reachable states are closed under steps](step-2.md)
- [Two-phase commit invariant](inv.md)
- [Multistep transitions preserve the two-phase commit invariant](inv-mtr.md)
- [The two-phase commit invariant holds in reachable states](inv-reachable.md)
- [Atomicity between participants](atomicity.md)
- [Validity for the coordinator](coord-committed-imp-all-voted-yes.md)
- [Validity for participants](committed-imp-all-voted-yes.md)
- [An aborted participant rules out a coordinator commit](aborted-imp-not-committed.md)
- [A committed participant has a committed coordinator](part-committed-coord-committed.md)
- [A committed coordinator has no aborted participant](coord-committed-part-not-aborted.md)
- [An aborted coordinator has no committed participant](coord-aborted-part-not-committed.md)
- [Atomic Commitment and Termination Detection](atomic-commitment-and-termination-detection/README.md)

## Related topics

- [FLP impossibility](../flp-impossibility/README.md): by the theorem of Fischer, Lynch and Paterson, every asynchronous commit protocol has a "window of vulnerability" in which the delay or crash of a single process can make it wait forever.
- [Atomic commitment and blocking of two-phase commit](atomic-commitment-and-blocking-of-two-phase.md)
