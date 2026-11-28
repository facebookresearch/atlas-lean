# Is Randomized Min Approximation

A randomized `α`-approximation for minimization uses `p.eval x.length` independent fair
bits on instance `x`. Its solver is polynomial time on the encoded pair of the instance and
tape, is feasible on every such tape, and has expected cost at most `α` times the minimum cost.
The polynomial tape length bounds the cost of generating the bits as well. Here `1 ≤ α`.
