# Cyclic Same Side Shortening inl

Cyclic same-side shortening for `Sum.inl` endpoints.

Orientation: word `L = Sum.inl cHead :: middle ++ [Sum.inl cLast]` with
`toStableE (prod L) = 1`. Rotate the last block to the front,
`Lrot = Sum.inl cLast :: Sum.inl cHead :: middle`, so `Lrot` starts with an
adjacent `inl`/`inl` pair.

Hypotheses: `n` arbitrary including `0`; `middle` may be `[]` (then
`L = [inl cHead, inl cLast]` of length 2). Shape forces length ≥ 2, so empty
and singleton are not inputs.

Conclusions:
- `toStableE (prod Lrot) = 1` (rotated kernel);
- with `Lnorm = normalizeBoundaryBlocks n Lrot`, `toStableE (prod Lnorm) = 1`;
- `Lnorm.length < L.length` via `length_normalizeBoundaryBlocks_lt_of_adjacent_inl`;
- `List.IsChain BoundaryBlocksAlternate Lnorm`;
- exact conjugacy `prod Lnorm = lastBlock * prod L * lastBlock⁻¹`
  (noncommutative, `lastBlock = lastBoundaryBlock n (Sum.inl cLast)`).

Nonclaims: no parity/odd-even, scalar pivot, finite-stage, Weyl, or Matsumoto
statement; does not claim `Lnorm` is `Pairwise` alternating or length ≤ 1;
does not claim the converse kernel transport without centrality.
