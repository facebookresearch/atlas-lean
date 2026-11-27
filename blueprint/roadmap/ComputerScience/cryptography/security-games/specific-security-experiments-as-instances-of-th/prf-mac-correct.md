# The PRF-MAC is correct

Let the key space `K` be finite and nonempty and the tags `T` have decidable
equality. For every `F : K → M → T`, the MAC `prfMac F` is correct: the honest
tag `F k m` always verifies (Katz and Lindell, Definition 4.1).
