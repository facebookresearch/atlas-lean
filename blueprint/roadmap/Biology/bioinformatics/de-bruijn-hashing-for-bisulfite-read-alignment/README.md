# De Bruijn hashing for bisulfite read alignment

Fingerprint indexes for approximate pattern matching in which hashes of overlapping $m$-mers overlap like the underlying strings (de Bruijn hash functions), so the hash of a text can be indexed in place of the text. Choosing the hash to be invariant under bisulfite conversions and to map Hamming balls into small Hamming balls supports fast alignment of bisulfite-treated reads.

- [Bisulfite-aware de Bruijn hash with Hamming control](bisulfite-aware-de-bruijn-hash-with-hamming-control.md)
