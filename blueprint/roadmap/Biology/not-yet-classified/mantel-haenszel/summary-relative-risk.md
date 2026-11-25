# Summary Relative Risk

The Mantel–Haenszel summary relative risk `R = ∑_k (A_k D_k / T_k) / ∑_k (B_k C_k / T_k)`. It is
meaningful when every total `T_k` and the denominator `∑_k B_k C_k / T_k` are positive; a zero
denominator gives `0` by Lean's convention `x / 0 = 0`.
