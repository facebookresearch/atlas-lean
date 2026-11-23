# Catchment budget closes

The catchment budget closes after area conversion: if the storage
change `ds`, expressed as an equivalent depth (storage volume per unit
catchment area), satisfies `ds = (p - e - q) * dt` for precipitation,
evaporation and runoff depth rates `p`, `e`, `q`, then the volume budget
`A * ds + (A * e) * dt + (A * q) * dt = (A * p) * dt` holds.
