# Bernoulli head directional deriv eq zero

Local form of Bernoulli's theorem: for steady incompressible inviscid flow
satisfying the Euler balance dotted with `u x`, with constant `ρ > 0` and
time-independent potential `Φ`, the directional derivative of the Bernoulli
head `p / ρ + ‖u‖^2 / 2 + Φ` along `u x` is zero at the point `x`. This is the
local differential condition behind `bernoulli_along_streamline`; by itself it
says nothing about the values of the head at other points.
