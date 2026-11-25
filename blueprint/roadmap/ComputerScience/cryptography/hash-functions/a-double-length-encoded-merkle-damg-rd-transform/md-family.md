# Keyed full Merkle-Damgård hash family

For a keyed compression function `C`, an initial value `iv`, a length-block
encoding `lenBlock` and a length-field size `L`, the keyed
double-length-encoded Merkle–Damgård hash `H^s(M) = fullHash (h^s) iv lenBlock
L M` on messages shorter than `maxLen`, a strengthened variant of Katz and
Lindell's Construction 5.3.
