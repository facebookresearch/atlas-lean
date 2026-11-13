# Exists Unique is Min On of strict Convex On

Existence and uniqueness of the minimizer (MF11.2): a function that is continuous and
strictly convex on a nonempty compact set `K` has exactly one minimizer on `K`. Convexity of `K`
is part of `StrictConvexOn`. Existence is `IsCompact.exists_isMinOn` and uniqueness is
`StrictConvexOn.eq_of_isMinOn`.
