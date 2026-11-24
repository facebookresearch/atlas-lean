# Sortslice Reverse Traced correct

The synchronized traced evaluator returns the exact range reversal while
retaining every safety, erasure, fuel, extent, and values-mode guarantee from
`sortsliceReverse_safe`.  The proof deliberately recovers the untraced result
through `ReverseSliceSafetyPost.exactErasure`, so correctness is about the same
execution whose accesses were checked.
