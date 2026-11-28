# Is Randomized Max Approximation

A randomized `α`-approximation for maximization uses `p.eval x.length` independent fair
bits on instance `x`. Its solver is polynomial time on the encoded pair of the instance and
tape, is feasible on every such tape, and has expected value at least `α` times the maximum value.
The polynomial tape length bounds the cost of generating the bits as well. Here `0 < α ≤ 1`.
