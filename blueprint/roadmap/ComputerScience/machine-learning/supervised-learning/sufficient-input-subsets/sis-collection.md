# SIS-collection procedure

`SIScollection`: while the remaining features `R` are sufficient (`τ ≤ g R`), find a SIS
among them, record it and mask it. Stops if `findSIS` returns an empty set (only possible
when `τ ≤ g ∅`).
