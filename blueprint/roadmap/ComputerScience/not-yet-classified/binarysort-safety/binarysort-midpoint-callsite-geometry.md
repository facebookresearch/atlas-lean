# Binarysort midpoint callsite geometry

Every active search iteration probes the arithmetic midpoint, and that
midpoint is a valid key-array index in the caller's range.  The two successor
intervals are strictly smaller and fit the predecessor fuel budget.
