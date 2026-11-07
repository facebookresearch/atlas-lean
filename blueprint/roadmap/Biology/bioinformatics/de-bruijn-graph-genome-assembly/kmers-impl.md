# Efficient executable computation of k-mers

Executable form of `kmers`: the suffixes of `s` are generated once by `List.tails`, so the
cost is `O(|s| · k)` rather than the `Θ(|s|²)` of recomputing `s.drop i` for every `i`. The
compiler uses it in place of `kmers` (`kmers_eq_kmersImpl`).
