# Real and reactive three-phase power through the power-factor angle

Let `Vm`, `Im`, `θ` and `φ` be real with `Vm ≥ 0` and `Im ≥ 0`. Take the
[balanced positive-sequence](balanced-phases.md) phase voltages built from `V = Vm e^{iθ}` and phase
currents built from `I = Im e^{i(θ - φ)}`, so that, with phasors rotating as `e^{iωt}`, the current
lags the voltage by the angle `φ`.
The sum `S` of the three phase [complex powers](complex-power.md) satisfies

- `Re S = 3 Vm Im cos φ`;
- `Im S = 3 Vm Im sin φ`;
- `Re S = √3 V_L I_L cos φ`, where `V_L = |V_ab|` is the magnitude of the
  [line-to-line voltage](line-voltage.md) `V_ab = V_a - V_b`, `I_L = |I_a|` the line-current
  magnitude and `√3` the positive square root.

The conditions `Vm ≥ 0` and `Im ≥ 0` make `Vm = |V|` and `Im = |I|`; the first two identities
hold without them. For RMS phasors under the passive sign convention, `Re S` and `Im S` are the
total real and reactive power absorbed and `cos φ` is the power factor; a current lagging by
`0 < φ < π` gives positive absorbed reactive power when `Vm Im > 0`. When `Vm = 0` or `Im = 0`
all three quantities are `0` for every `φ`, and `φ` is not determined by the phasors.
