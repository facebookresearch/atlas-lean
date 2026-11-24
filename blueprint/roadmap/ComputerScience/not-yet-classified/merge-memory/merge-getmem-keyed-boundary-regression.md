# Merge Getmem keyed boundary regression

Keyed storage has the exact worst-case allocation limit `2^59 - 1` on the
selected 64-bit platform. If the boundary request reaches the allocation path,
it grows, while the next request also reaches that path and is rejected.
