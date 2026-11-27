# Boolean circuits for HQC fixed-weight sampling

The finite-width HQC support sampler is computed exactly (not approximately) by a Boolean circuit family generated uniformly in polynomial time: the candidate for word $i$ is the multiply-high $i + \lfloor a_i (n - i)/2^b \rfloor$, computed by widening the product before selecting the high bits (an exact multiplier and carry-lookahead adder); each collision-correction step compares the current candidate with one corrected later entry using equality comparators of $O(b)$ gates and replaces a collision by the offset through a multiplexer of $O(b)$ gates; the descending scan performs one comparison for each pair of positions, reusing corrected entries in the source's loop order; and a final stage converts the corrected words into the weight-$w$ indicator vector. The circuit has $O(w^2 b)$ gates for the correction stage, and on every input it outputs the same support as the sequential algorithm, so the circuit family has exactly the finite sampler's output law.

## Proof sketch

Each gadget is verified against the arithmetic it implements on fixed-width words; the composition follows the nested loops of the specification.

## Depends on

- [Fixed-weight support sampling in HQC](hqc-fixed-weight-sampling.md)

## Sources

- Philippe Gaborit et al., "Hamming Quasi-Cyclic (HQC)", Version 5.1, November 9, 2026.
