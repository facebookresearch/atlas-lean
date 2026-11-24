# Bit-vector column correctness

**Bit-vector column correctness** (Myers 1999, Figure 5): same setup as
`delta_range`, plus per-column bit-vectors (`Pv`, `Mv`), equality masks
(`Eq`: bit `i` iff `P[i] = T[j]`), and the step correctness (`hstep_ok`:
the step outputs encode exactly the true deltas). Conclusion: the reported
positions are exactly the matches within `k` differences.

## Sources

- Myers (1999), Figure 5.
