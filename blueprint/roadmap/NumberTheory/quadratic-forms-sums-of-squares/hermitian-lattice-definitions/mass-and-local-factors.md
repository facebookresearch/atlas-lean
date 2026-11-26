# Mass and local factor evaluations

For a definite Hermitian form `h` and a full lattice
`L`, `MassAndLocalFactors` bundles two functions:

- `mass` returns a rational number given finiteness of the global isometry classes in the genus
  of `L` and finiteness of the unitary stabilizer of every lattice in that genus.
- `localFactor` returns a real number given integrality of `L`, a nonzero prime `p` of the
  base ring of integers, finite length of the completed dual quotient over the completed base
  ring at `p`, and a real density together with a witness that the normalized counts converge
  to it and a proof that it is nonzero.

The field types do not establish these premises or constrain the returned values to particular
formulas. The function `massAndLocalFactors` supplies the mass and local factor formulas.
