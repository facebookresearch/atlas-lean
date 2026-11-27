# HMAC forgery is invariant under injective message encodings

Let the chaining values `S` have decidable equality and
the messages `X` have decidable equality. For an injective encoding `enc : X →
List Bool` and a forger `A` against the HMAC scheme on `enc`, the forgery
experiment of HMAC on all bit strings against `A` relabeled along `enc` equals
the forgery experiment of the HMAC scheme on `enc` against `A`; freshness of
the forged message is preserved because `enc` is injective.
