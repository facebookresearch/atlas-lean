# Gain lt one all frequencies

All-frequency gain threshold for the car-following transfer
function: the gain `‖λ * exp (-(I * w * T))‖ < ‖denom λ T w‖`
holds at every positive frequency `w` if and only if
`lambda * T ≤ 1 / 2`. This composes `CarFollowingGain.gain_lt_one_iff`
with `CarFollowingGain.gain_threshold_all_frequencies`.
