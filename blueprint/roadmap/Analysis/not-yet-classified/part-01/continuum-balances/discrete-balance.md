# Finite-volume balance

**Finite-volume balance** (MF08.1). Cell `i : Fin n` of a chain of cells of common width
`Δx` lies between the faces `i.castSucc` (left) and `i.succ` (right), and `F j` is the flux
through face `j`, positive towards increasing index; `F 0` and `F (Fin.last n)` are the left
and right boundary fluxes. The concentration in cell `i` changes at the rate
`-(F (i + 1) - F i) / Δx`, inflow minus outflow per unit width. The width is a positive real,
so zero and negative cell widths cannot be supplied to this API.
