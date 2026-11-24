# Cell transmission model of traffic flow

## Demand, supply and face flux

- [Capacity v w kj / (v + w) of the triangular fundamental diagram](capacity.md)
- [Sending demand min(v k, capacity) of a cell](demand.md)
- [Receiving supply min(w (kj − k), capacity) of a cell](supply.md)
- [Face flux: the smaller of upstream demand and downstream supply](face-flux.md)
- [With admissible densities and positive speeds the face flux is ≥ 0](face-flux-nonneg-of-le.md)
- [The face flux never exceeds the upstream demand](face-flux-le-demand.md)
- [The face flux never exceeds the downstream supply](face-flux-le-supply.md)
- [For k ≥ 0 and positive speeds, 0 ≤ demand ≤ capacity](demand-nonneg-le.md)
- [For k ≤ kj and positive speeds, 0 ≤ supply ≤ capacity](supply-nonneg-le.md)
- [Demand and supply both equal the capacity at the critical density](capacity-attained.md)

## One update step

- [Under the CFL condition one update keeps the density between 0 and kj](update-mem-icc.md)

## Turning flows at junctions

- [Downstream boundary flow of a commodity on a link](link-outflow.md)
- [Upstream boundary flow of a commodity on a link](link-inflow.md)
- [Turning fraction of a commodity between two links](turning-fraction.md)
- [Junction-local receiving constraint of a turning certificate](is-supply-feasible.md)
- [Aggregate conservation at a junction](sum-link-outflow-eq-sum-link-inflow.md)
- [The upstream boundary flow of a link is at most its supply](sum-link-inflow-le-supply.md)
- [Spillback: no turning flow into a link whose first cell is jammed](eq-zero-of-k-first-eq-kj.md)
- [Turning flows are turning fractions times the outflow](turning-fraction-mul-link-outflow.md)
- [Incidence transfer of the aggregate turning flows](incidence-matrix-mul-vec-turning-flow.md)
- [Route certificates are supported on movements](eq-zero-of-route.md)
