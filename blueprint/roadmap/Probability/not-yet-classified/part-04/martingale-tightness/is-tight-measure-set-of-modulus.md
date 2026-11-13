# Tightness in `C((0,1))` from a modulus-of-continuity bound

**Tightness in `C([0,1])` from a modulus-of-continuity bound** (Billingsley 1999,
Theorem 7.3, with the paths pinned at `0`). If every `W n` vanishes at time `0` and, for all
`ε, b > 0`, there is `δ > 0` such that eventually
`P(∃ s t, |s - t| ≤ δ, |W n s - W n t| ≥ ε) ≤ b`, then the laws of `W n` are tight.

The proof is Arzelà–Ascoli: the paths outside a small exceptional set lie in a closed
uniformly bounded equicontinuous family (the bound comes from chaining the modulus from `0`),
and the finitely many early laws are tight individually because `C([0,1])` is Polish.
