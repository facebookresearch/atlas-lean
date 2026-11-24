# Face flux: the smaller of upstream demand and downstream supply

For a free-flow speed `v`, a wave speed `w`, a jam density `kj` and the densities `k_up` of the
upstream cell and `k_down` of the downstream cell (real numbers), the flux through the face between
them is `min(D(k_up), S(k_down))`, the smaller of the upstream [demand](demand.md)
`D(k_up) = min(v k_up, v w kj / (v + w))` and the downstream [supply](supply.md)
`S(k_down) = min(w (kj - k_down), v w kj / (v + w))`.
