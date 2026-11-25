# Sum lookup With Cost mod Prime time mul le of mem

Let `p` be prime and `m > 0`, and let `n` be the number of distinct keys of a list of entries with keys in `ZMod p`. For a key present among them, the lookup time summed over the `p(p - 1)` hash functions of the mod-prime family, each used to build the table from the list, times `m`, is at most `p(p - 1)(m + n - 1)`.
