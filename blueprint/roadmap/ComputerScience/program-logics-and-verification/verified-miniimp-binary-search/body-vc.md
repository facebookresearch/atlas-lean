# Verification condition of the binary-search loop body

If a state `s` satisfies the binary-search invariant and the loop guard holds,
then `s` satisfies the weakest precondition of the loop body for the
invariant: the body's array read is in bounds and the invariant holds
afterwards.
