# The catchment water budget closes in volume units

Let `A` be a catchment area, `p`, `e` and `q` precipitation, evaporation and runoff depth rates,
`dt` a duration and `ds` a storage change expressed as an equivalent depth (storage volume per unit
catchment area), all real numbers. If `ds = (p - e - q) * dt`, then the volume budget
`A * ds + (A * e) * dt + (A * q) * dt = (A * p) * dt` holds.
