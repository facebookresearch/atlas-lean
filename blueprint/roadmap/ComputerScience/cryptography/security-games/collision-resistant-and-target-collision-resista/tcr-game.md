# Target collision resistance

**Target collision resistance** (universal one-way hashing; Katz and Lindell, Section 5.1):
the adversary commits to `x`, then `s ← Gen` is revealed and it outputs `x'`; the experiment
outputs `1` when `x' ≠ x` and `H^s(x) = H^s(x')`.
