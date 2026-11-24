# Bending Torsion Calibrated

A supplied yield functional (tension positive) is calibrated on the bending-torsion states
with shear factor `c` when `c` is positive and the functional returns `√(σ ^ 2 + c τ ^ 2)` on every
such state: `c = 3` for the von Mises (distortion-energy) criterion, `c = 4` for the Tresca
(maximum-shear) criterion. A factor `c ≤ 0` is excluded: `Real.sqrt` truncates negative arguments
to `0`, so a pure torque would have zero demand.
