# Scores along a diagonal from a given cell

For a real score `s` on pairs of letters, words `u` and `v` and natural numbers `i` and `j`, the
diagonal list from the cell `(i, j)` is `s(u_i, v_j), s(u_{i+1}, v_{j+1}), …`, continued until
either word ends (positions are counted from `0`). It has `min(|u| - i, |v| - j)` entries, with
truncated subtraction (`a - b = 0` for `b ≥ a`), so it is empty when `i ≥ |u|` or `j ≥ |v|`.
