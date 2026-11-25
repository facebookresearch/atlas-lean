# Blocks Fuel

Cut at most `k` consecutive `n`-bit blocks off the front of a bit string, stopping when fewer
than `n` bits remain. Each step inspects only the first `n` bits (`(P.take n).length = n` holds
exactly when `n ≤ |P|`) and never the length of the remaining list, so `blocksFuel k P` runs in
time `O(k * n)`.
