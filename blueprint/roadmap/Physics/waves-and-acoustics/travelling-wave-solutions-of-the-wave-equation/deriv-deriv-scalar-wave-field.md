# Deriv deriv scalar Wave Field

The iterated Physlib time derivative of a transported field is the second `t`-derivative:
if the slice `fun s => φ s (x 0)` has derivative `φt s (x 0)` at every `s`, and
`fun s => φt s (x 0)` has derivative `φtt t.val (x 0)` at `t.val`, then the second time
derivative in `ClassicalMechanics.WaveEquation` has component `φtt t.val (x 0)`.
