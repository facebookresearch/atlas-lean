# MAC from a pseudorandom function

Let the key space `K` be finite and nonempty and the tags `T` have decidable
equality. For `F : K → M → T`, `prfMac F` is the deterministic MAC with
uniformly random key `k` and tag `Mac_k(m) = F k m`; verification recomputes
the tag (Katz and Lindell, Construction 4.5).
