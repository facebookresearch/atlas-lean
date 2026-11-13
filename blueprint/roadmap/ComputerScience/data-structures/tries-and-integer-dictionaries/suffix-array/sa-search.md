# Suffix-array search for a pattern's row interval

Suffix-array search (Manber and Myers 1993): the row interval `[sp, ep)` of the suffixes of
`s` that start with `P`, found by two binary searches over the rows `[0, |s|)`. The suffix
array is computed once and shared by both searches.
