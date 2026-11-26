# Synchronous protocol over lossy links

A deterministic protocol for the processes `G`
with inputs and decisions in `V`, local states `σ` and messages `M`. Process `i` starts in state
`init i x` from its input `x`. In round `r`, process `j` in state `s` sends `send r j s i` to
process `i`, `none` meaning no message, and process `i` in state `s` moves to `recv r i s msg`,
where `msg j` is the message it received from `j`, or `none` if it received none. At the end,
process `i` in state `s` decides `output i s`.
