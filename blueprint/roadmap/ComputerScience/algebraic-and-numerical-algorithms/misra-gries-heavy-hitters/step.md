# Step

One Misra-Gries step with parameter `k` (core of ALG-26b). The state is a summary of
stored `(item, counter)` entries plus the number of decrement rounds so far. Processing `x`:
if `x` has a positive counter or fewer than `k - 1` entries are stored, replace the entry of `x`
by one with its counter one higher (a new item enters with counter `1`); otherwise decrement
every stored counter, drop the entries that reach `0`, and record a round.
