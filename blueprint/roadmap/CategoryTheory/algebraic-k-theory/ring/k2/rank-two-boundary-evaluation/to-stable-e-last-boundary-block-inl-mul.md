# To Stable E last Boundary Block inl mul inr mem range imp eq one

Arbitrary-rank general-ring: `toStableE (lastBoundaryBlock n (inl c) *
lastBoundaryBlock n (inr r))` in `E_n` forces `c=1`, `r=1`. Reuses core forcing
`toStableE_lastColumnRow_product_mem_range_imp_eq_one` and `lastBoundaryBlock_inl`/`inr`;
no alternating-word, no torus mult, no cocycle, no kernel; ordered product preserved.
