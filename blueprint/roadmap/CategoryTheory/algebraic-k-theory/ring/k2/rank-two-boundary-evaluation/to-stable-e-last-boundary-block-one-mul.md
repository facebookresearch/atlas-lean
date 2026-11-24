# To Stable E last Boundary Block one mul one eq one imp

Fin-2 consumer: `toStableE (lastBoundaryBlock 1 (inl c) *
lastBoundaryBlock 1 (inr r)) = 1` forces `c = 1` and `r = 1` over a field.

**Prominent nonclaims:**
* does **not** normalize arbitrary `finiteStage 2` words;
* does **not** prove the rank-two kernel base.
Reuses `toStableE_lastBoundaryBlock_inl_one`,
`toStableE_lastBoundaryBlock_inr_one`, `fromFinite_injective`,
and explicit `2 × 2` entries `E01(a)*E10(b)=[[1+a*b,a],[b,1]]`.
