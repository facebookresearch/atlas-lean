# FM-index backward search

FM-index backward search: the half-open row interval `[sp, ep)` for a pattern, computed from
the last column alone, processing the pattern from its last letter to its first. The interval for
the suffix and `C[c]` are each computed once per letter, so a pattern of length `m` makes `m`
recursive calls.
