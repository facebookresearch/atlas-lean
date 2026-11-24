# Leaky integrate-and-fire first hit

For the trajectory
`u(t) = uinf - (uinf - ur) * exp (-t / tau)` from reset `ur` toward
`uinf`, with `ur < theta`, `tau > 0` and `uinf > theta`, the first
threshold hit is `T = tau * log ((uinf - ur) / (uinf - theta)) > 0`:
`u(T) = theta` and `u(t) < theta` for `0 ≤ t < T`.
