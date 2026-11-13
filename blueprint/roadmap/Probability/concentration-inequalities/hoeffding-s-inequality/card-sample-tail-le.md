# Hoeffding's bound for sampling without replacement

Hoeffding's upper-tail bound for sampling without replacement, stated as a count.

Among the `n`-element subsets `S` of `s`, at most
`exp (-2 * n * t ^ 2) * choose (#s) n` satisfy
`n * mean(c) + t * n * R ≤ ∑ i ∈ S, c i`. The event is non-strict; `n = 0` and
`#s < n` are included without separate assumptions.
