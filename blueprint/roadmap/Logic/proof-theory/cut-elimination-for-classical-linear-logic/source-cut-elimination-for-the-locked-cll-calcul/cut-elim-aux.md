# Cut elimination by structural recursion on the proof

Cut-free proofs are computed by structural recursion on an arbitrary proof: each case first
normalises the premises, then applies cut admissibility at each cut. The sequent of the current
subgoal is carried as an explicit list.
