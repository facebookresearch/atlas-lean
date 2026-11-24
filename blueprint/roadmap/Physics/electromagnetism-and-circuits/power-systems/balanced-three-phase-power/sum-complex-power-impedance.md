# Total complex power of a balanced load with equal phase impedances

Let `V` be complex and `Z` a nonzero complex impedance. Feed equal impedances `Z` with the
[balanced positive-sequence](balanced-phases.md) phase voltages `(V_a, V_b, V_c) = (V, α² V, α V)`,
with `α = e^{2πi/3}`, so that phase `p` draws the current `V_p / Z`. The phase
[complex powers](complex-power.md) sum to

`V_a conj(V_a / Z) + V_b conj(V_b / Z) + V_c conj(V_c / Z) = 3 |V|² / conj(Z)`,

where `conj` denotes complex conjugation. For RMS phasors under the passive sign convention this is
the total complex power absorbed by the load. A passive load has `Re Z ≥ 0`; the identity holds for
every nonzero complex `Z`.
