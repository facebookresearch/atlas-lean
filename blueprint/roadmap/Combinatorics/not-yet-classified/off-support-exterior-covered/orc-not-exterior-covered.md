# Orc not exterior Covered

`StatMech.Lattice.orc_ExteriorCovered` never holds. If the beacon is off `Vc`, its component
contains only sites off `Vc`, but a vertex of `Vc` in its leftmost column is outside. If the beacon
is on `Vc`, its component is the beacon alone, but the site just left of that vertex is outside and
off `Vc`.
