# Eventually surjective transitions imply the Mittag–Leffler condition

Let `R : Type u` be a ring and `A : ℕᵒᵖ ⥤ ModuleCat.{w} R`. If there exists `N : ℕ` such that
each successor transition `A.map (homOfLE (Nat.le_succ n)).op` is epi whenever `N ≤ n`, then
`A.IsSequentialMittagLeffler`; the images of later terms in each fixed `A_m` eventually
stabilize.
