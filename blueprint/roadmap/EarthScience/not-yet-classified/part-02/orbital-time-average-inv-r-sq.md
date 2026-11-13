# Orbital Average

Annual average of `1 / r²` for a stipulated elliptic orbit. With
`0 ≤ e < 1`, `a > 0`, `r θ = a * (1 - e²) / (1 + e * cos θ)`, areal-law
time weighting `dt ∝ r² dθ` with areal constant `h > 0`, and the stipulated
area integral `∫ θ in 0..2π, (r θ)² = 2π * a² * √(1 - e²)` (the ellipse
area integral, taken as a hypothesis, not proved here), the time-weighted
average of `1 / r²` over one period is `1 / (a² * √(1 - e²))`.
