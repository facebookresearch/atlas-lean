# Gauss

The Gaussian solution on the line with total mass `M`:
`gauss M D x t = M / √(4πDt) · exp(-x² / (4Dt))`. It is meant for `D > 0` and `t > 0`. For
`D > 0` and `t ≤ 0` the square root is `0` and Lean's convention `M / 0 = 0` makes the value `0`.
It is the point-release kernel of `PhyslibExt.EarthScience.PointRelease` with no drift and no
reaction.
