# Did Estimand

The 2×2 difference-in-differences estimand of Roth et al. (2023), eq. (2):
`E[Y_post - Y_pre | G] - E[Y_post - Y_pre | Gᶜ]`, where `G` is the treated group and the
conditional means are set averages over the group events. For a probability measure with
`0 < μ G < 1` and integrable outcomes these are the conditional means of the source; if a group
has measure `0` or `∞`, or the difference is not integrable on it, its set average is Mathlib's
junk value `0`.
