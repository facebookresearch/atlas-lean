# Martingale Part succ sub

The increment of the compensated process `M = N - A` (Mathlib's `martingalePart`, with the
compensator `A = predictablePart N`) is `ΔN_{n+1} - E[ΔN_{n+1} | ℱₙ]`.
