# Bloom filter

A Bloom filter over a type $\alpha$ with $m$ bits consists of a finite list of
hash functions $\alpha \to \{0, \dots, m - 1\}$ and a bit vector of length $m$.

No false-positive rate is claimed because the model supplies no probability distribution.
