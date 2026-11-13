# Delayed Entry Data

Left-truncated survival data on `k` grid times: subject `i` enters at grid index `entry i`
(`⊥` = before `t₀`, see `entryIndex`), leaves at `time (exit i)`, with an event iff `event i`.
Only subjects entering strictly before they leave are included.
