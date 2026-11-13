# Sampled-suffix-array locate is correct

If every stored value is correct
(`sample r = some v → v = SA[r]` for rows `r ≤ |t|`) and every row of text position `0` is
sampled, then `locate` returns `SA[r]` for every row `r ≤ |t|`.
