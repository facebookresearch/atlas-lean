# Locate takes at most `s - 1` steps

For `0 < s`, if every row whose text position is
a multiple of `s` is sampled, then from row `r ≤ |t|` locate makes at most `SA[r] mod s` LF
steps (for any amount of fuel `k`). At `s = 0` the `s - 1` bound would be `0` while the
proof only gives `SA[r] mod 0 = SA[r]` steps.
