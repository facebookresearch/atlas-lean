# FKS primary hash

**FKS primary hash** (CLRS, Section 11.5). A universal family hashing the keys `K` into
`n = |K|` buckets has a member with fewer than `n` ordered collisions
(`∑ b, n_b (n_b - 1) < n`), so its squared bucket sizes sum to less than `2 n`: with
secondary tables of sizes `n_b²`, the two-level scheme then uses linear total space.
