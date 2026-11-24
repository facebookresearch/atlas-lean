# Rail Limited Map

The rail-limited feedback map at input `vi`:
`F(vo) = clamp(vmin, vmax, A * (vi - beta * vo))`. A fixed point
`vo = F(vo)` is the leaf's operating point; no dynamics are modeled.
