# Pore velocity from Darcy flux and porosity

For a Darcy discharge per bulk area `q` and a porosity `n` (real numbers), the pore (seepage)
velocity is `v = q / n`. The Darcy flux and the pore velocity are different quantities; this is
only the kinematic conversion between them. It is defined for every real `n`, with the convention
`x / 0 = 0`: at `n = 0` the value is `0`. Physical porosities satisfy `0 < n ≤ 1`.
