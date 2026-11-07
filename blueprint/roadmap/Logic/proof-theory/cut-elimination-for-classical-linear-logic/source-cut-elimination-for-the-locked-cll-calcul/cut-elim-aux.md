# Cut elimination by structural recursion on the proof

Compute cut-free proofs by structural recursion on the original (possibly
non-cut-free) proof. Each case recursively normalises the premises, then uses
`cutAdm` at each cut. The list `Γ` is the explicit sequent for the current subgoal.
