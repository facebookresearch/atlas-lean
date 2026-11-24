# Dual Vector

LP dual vector of a dispatch dual witness, in the row order of the
canonical LP. The nodal prices `lam` are free multipliers of the balance
`L_b * θ - Cgen * pg = -d`: their positive parts go to the first balance
block and their negative parts to the second. The free reference
multiplier `ρ` is split the same way over the two reference rows. The
generator and flow bound multipliers `μhi, μlo, ηhi, ηlo` are passed
unchanged, so a negative entry fails the checker's sign test.
