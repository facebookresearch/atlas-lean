# Is Uniform KDF

A **uniform key-derivation function**: `H` maps a uniform element of `G` to a uniform element
of `K`. This is the minimal assumption under which hashing a uniform Diffie–Hellman key yields a
uniform symmetric key (Katz and Lindell, Section 11.4.2, use a hash function with this property).
Wave 3: unify with the ROM lane's KDF.
