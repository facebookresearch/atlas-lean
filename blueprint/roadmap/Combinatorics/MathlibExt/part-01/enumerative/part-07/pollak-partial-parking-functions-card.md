---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.PollakPartialParking.pollak_partial_parking_functions_card
---

# Pollak Partial Parking Functions

Pollak's circle trick for partial parking functions: for positive `s ≤ t`,
the number of preference lists `f : Fin s → Fin t` satisfying the standard
successful-parking threshold characterization (for every zero-based spot `k`,
at most `t - k` cars prefer a spot at or after `k`) is
`(t + 1 - s) * (t + 1) ^ (s - 1)`.

Provenance (independently verified):

- Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, and
  Marshall Moats, “Lucky Cars and Lucky Spots in Parking Functions”,
  Journal of Integer Sequences 29 (2026), Article 26.1.1.
- Source URL: https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.tex
- Proposition at source lines 330–332.
- Full source SHA-256:
  d166e7759bfd986aebf8bd5632479d9f5e4f11b28f5250ed1e5290851a8d6139
- Normalized no-final-newline proposition-span SHA-256:
  58e90130ad683625acf4a657d5bbbf145f2700065e2991cfd7084425783cc1fe

## Depends on

- [Is Partial Parking Function](../part-06/parking-function/is-partial-parking-function.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.PollakPartialParkingFunctions](../../../../../../sources/v2/MathlibExt.md)
