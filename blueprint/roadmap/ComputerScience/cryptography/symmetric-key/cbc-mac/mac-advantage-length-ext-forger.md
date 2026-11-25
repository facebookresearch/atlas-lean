# Basic CBC-MAC is insecure for variable-length messages

**Basic CBC-MAC is insecure for variable-length messages** (Katz and Lindell, Section 4.4.1):
against every block cipher, the length-extension forger, with one query, forges with
probability `1`: the tag of `[x, x - t]` is `F_k (F_k x + x - t) = F_k x = t`.
