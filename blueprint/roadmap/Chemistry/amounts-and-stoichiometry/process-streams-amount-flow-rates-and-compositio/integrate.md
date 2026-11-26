# Amounts accumulated by running a constant stream for a duration

For a [process stream](stream-flow.md) with species flow rates `ṅ i` and a real duration `Δt`, the
accumulated amounts are the vector with entry `Δt * ṅ i` for each species `i`: the amount of each
species collected while the stream runs at these constant rates for a time `Δt`. The definition
allows every real `Δt`: `Δt = 0` gives zero amounts, and for a negative `Δt` the entries `Δt * ṅ i`
are not collected amounts; the physical reading needs `0 ≤ Δt`.
