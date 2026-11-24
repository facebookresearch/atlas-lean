# Evanescent Mode satisfies mode Equation

Sinusoidal profile and the exponential mode
`cos (freq t) exp (-alpha z)` satisfy the mode equation exactly
under `freq^2 = c0^2 (kc^2 - alpha^2)`. No sign is imposed on
`alpha`: the mode is evanescent (decaying along the guide) exactly
when `0 < alpha`, see `evanescentMode_decay`; `alpha = 0` gives a
mode independent of `z` and `alpha < 0` a growing one.
