# Front-yard and back-yard hash table design

In the *front-yard/back-yard* paradigm, a hash table for up to $n$ keys consists of a *front yard*: an array of $n/h$ bins, each with capacity somewhat above the mean load $h$, with each key hashed to one bin by a single hash function, and a *back yard*: a separate dynamic dictionary that stores the keys whose front-yard bin is full. Queries look in the key's bin and then in the back yard; the back yard is designed to hold only $o(n)$ keys, so it may use a less space-efficient structure. Iceberg hashing uses bins of capacity $h + \tau_h$ with $\tau_h = k\sqrt{h \log h}$ for a large constant $k$, and leaves the back yard *unmanaged*: a key placed there stays there even after space frees up in its bin.

## Depends on

- [Stable hash tables](stable-hash-table.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, William Kuszmaul, Guido Tagliavini, "Iceberg Hashing: Optimizing Many Hash-Table Criteria at Once", Journal of the ACM 70(6) (2023), arXiv:2109.04548.
