# State Spec

The specified Aho–Corasick state after reading `w`: the longest suffix of `w` that is a prefix
of some pattern, with the empty list, always a suffix, as the fallback. `w.tails` lists the
suffixes of `w` longest first, so this is the first suffix that passes the test.
