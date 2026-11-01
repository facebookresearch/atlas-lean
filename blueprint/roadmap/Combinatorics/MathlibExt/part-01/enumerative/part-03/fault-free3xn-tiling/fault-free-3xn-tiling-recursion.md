---
article_id: af_312ebd37227fb9c792e853ea
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.fault_free_3xn_tiling_recursion
---

# Fault free 3xn tiling recursion

For `n ≥ 1`, the independently defined number of vertical-fault-free
square-and-domino tilings equals the sequence with initial values
`3, 13, 26, 66, 154, 380` and recurrence
`V_n = V_{n-1} + 4 V_{n-2} - V_{n-3} - V_{n-4}`.

Proof: The count is encoded by a transfer matrix over column profiles. An annihilating
polynomial for that matrix gives the recurrence after the six initial values.

## Depends on

- [Tiling Count](tiling-count.md)
- [Vertical Fault Free Tiling Count](vertical-fault-free-tiling-count.md)

## Proof depends on

- [Is Square Domino Tiling](is-square-domino-tiling.md)
- [Is Square Or Domino](is-square-or-domino.md)
- [Is Vertical Fault Free](is-vertical-fault-free.md)
- [Tiling Cell](tiling-cell.md)
- [Adjacent](adjacent.md)
- [Is Square Or Domino iff](is-square-or-domino-iff.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.FaultFree3xnTiling](../../../../../../../sources/v2/MathlibExt.md)
- Oluwatobi Jemima Alabi and Greg Dresden, "Fault-Free Tilings of the 3 × n Rectangle With Squares and Dominos," Journal of Integer Sequences 24 (2021), Article 21.1.2, theorem on vertical-fault-free `V_n` (unlabeled), lines 358–364, <https://cs.uwaterloo.ca/journals/JIS/VOL24/Dresden/dresden7.tex>.
