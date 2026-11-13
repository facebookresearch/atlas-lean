# Encode Length

The `w`-bit little-endian encoding of `n`: least significant bit first, bits at positions
`≥ w` dropped. This is the length field `⟨L⟩` of Katz and Lindell, Construction 5.3, in a
configurable width. It is the reversal of the canonical big-endian codec `Nat.toBitsBE`.
