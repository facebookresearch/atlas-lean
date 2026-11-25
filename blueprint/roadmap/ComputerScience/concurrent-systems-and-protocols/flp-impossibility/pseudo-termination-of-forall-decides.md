# Deciding runs give reachable decisions

Let the set of processes be finite with at least two processes, and let $a$ be an algorithm such that every admissible run of $a$ with at most one faulty process decides (some process decides at some time). Then from every state reachable from an input assignment, a decision can be reached by steps that receive only messages addressed to the processes of any given set that misses at most one process.

This is the step at which the FLP proof uses its contradiction hypothesis: a fair run of the processes outside one process, from a reachable state, is admissible with at most one faulty process, so it decides. The run is built by a fair scheduler that delivers, stage by stage, every pending message addressed to the processes of the set.

## Sources

- The argument is adapted from the proof, in the CSLib formalization of the FLP theorem, that consensus algorithms are pseudo-consensus algorithms (`Cslib.FLP.PseudoConsensus.of_consensus`).
