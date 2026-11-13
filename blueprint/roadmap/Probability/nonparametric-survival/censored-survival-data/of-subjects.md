# Of Subjects

Grouped censored data from per-subject records: subject `i` is observed at `time (group i)`,
with an event if `δ i = true` and censored if `δ i = false`. The counts are
`deaths j = #{i | group i = j ∧ δ i = true}` and `censored j = #{i | group i = j ∧ δ i = false}`.
