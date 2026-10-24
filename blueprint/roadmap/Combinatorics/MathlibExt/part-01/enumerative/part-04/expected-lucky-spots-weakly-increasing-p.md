---
article_id: af_c4b89ad3d893f5e2081f9b09
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.expected_lucky_spots_weakly_increasing_parking_functions
---

# Lucky Parking Functions

The uniform average number of lucky cars/spots among weakly increasing
parking functions of length `n` is `3n / (n + 2)`. A weakly increasing
parking function is encoded 0-based as a monotone `a : Fin n → Fin n` with
`a i ≤ i`; the `i`-th car parks in spot `i` and is lucky exactly when
`a i = i`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.LuckyParkingFunctions](../../../../../../sources/v2/MathlibExt.md)
- Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, and Marshall Moats, "Lucky Cars and Lucky Spots in Parking Functions," Journal of Integer Sequences 29 (2026), Article 26.1.1, Corollary, lines 631–633 (supporting lemma lines 619–629), https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.tex The corollary attributes the Dyck-path expectation value to Deutsch.
