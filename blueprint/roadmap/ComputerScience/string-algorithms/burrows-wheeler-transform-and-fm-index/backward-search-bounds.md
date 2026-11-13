# Backward search returns a genuine row interval

Backward search always returns a genuine interval of rows, `sp ≤ ep ≤ |L|`, on any list `L`
(so the difference in `backwardSearch_count` involves no truncated subtraction).
