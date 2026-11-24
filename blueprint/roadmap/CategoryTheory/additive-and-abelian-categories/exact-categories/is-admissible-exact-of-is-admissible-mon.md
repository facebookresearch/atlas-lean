# Is Admissible Exact of is Admissible Mono is Colimit

An admissible-mono first leg plus a cokernel colimit second leg imply admissible exactness.

For `S : ShortComplex C`, `hf : IsAdmissibleMono S.f` and
`hc : IsColimit (CokernelCofork.ofπ S.g S.zero)` suffice for `IsAdmissibleExact S`.
Unpacks `hf` to `W, p, w, hS'`, reuses the canonical cokernel comparison
`hc'.coconePointUniqueUpToIso hc`, derives the second-leg equation with
`IsColimit.comp_coconePointUniqueUpToIso_hom`, then transports with
`ShortComplex.isoMk` and `isAdmissibleExact_of_iso`.
