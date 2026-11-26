# Savitch's midpoint recursion with an explicit stack

On configurations encoded as words of width $w$, reachability within $2^{d}$ steps of a step relation can be decided by the midpoint recursion "reachable within $2^{i+1}$ steps iff some midpoint is reachable within $2^i$ steps from the start and reaches the target within $2^i$ steps", run with an explicit stack of at most $d$ frames of $O(w)$ bits each, enumerating midpoints in a fixed order. The same stack discipline turns a positive answer into a walk that visits the configurations of a witnessing path in order while storing only the pending targets with their levels, so space stays $O(d w)$.

## Depends on

- [Savitch's theorem: NPSPACE = PSPACE](../../../../TheoryOfComputation/complexity-classes/savitch.md)

## Sources

- W. J. Savitch, "Relationships between Nondeterministic and Deterministic Tape Complexities", Journal of Computer and System Sciences 4(2), 1970.
- M. Sipser, "Introduction to the Theory of Computation", 3rd ed., Cengage Learning, 2013.
