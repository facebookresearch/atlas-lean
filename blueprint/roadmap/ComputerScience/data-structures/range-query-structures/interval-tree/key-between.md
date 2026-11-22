# Key between optional bounds

Given an optional lower bound, an optional upper bound and a
key $k$ (a pair of an integer and a natural number), this test returns true exactly when the lower
bound is absent or strictly below $k$, and the upper bound is absent or strictly above $k$. Keys
are compared lexicographically: first by the integer, then by the natural number.
