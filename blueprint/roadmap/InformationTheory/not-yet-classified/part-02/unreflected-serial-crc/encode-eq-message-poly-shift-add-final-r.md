# Encode eq message Poly shift add final Register

The register computes exactly the check remainder that the polynomial
encoder `Cslib.CodingTheory.CRC.encode` appends: the codeword is the shifted
message plus the final register read as a polynomial (characteristic two, so
appending is addition).
