# Padding is injective

**Padding is injective** for every block length `B`, length-field width `L`, and message, with
no bound on the message length (Katz and Lindell, Construction 5.3: distinct inputs give distinct
padded strings). Dropping the `L`-bit length field leaves `M ++ 1 0…0`, and the last `1` bit marks
the end of `M`; the length field is not read, so `|M| ≥ 2 ^ L` is allowed.
