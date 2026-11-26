# To Canonical

Canonical-pullback consumer: transport to the canonical pullback projection.

Given `h` over `f : B' ⟶ B`, this returns a fixed-fiber presentation of the
canonical `Limits.pullback.snd p f` with the same fiber `F`, via the unique
isomorphism `(h.sq.isoIsPullback _ _ (IsPullback.of_hasPullback p f)).symm`
and the exact commuting equation
`(h.sq.isoIsPullback _ _ _).inv ≫ h.p' = Limits.pullback.snd p f`
(`IsPullback.isoIsPullback_inv_snd`). The ambient square is retained as the
source of the iso; no product limit is reproved.
