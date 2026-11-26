# Cut multisets containing every descent boundary

Let `n : ℕ`, `σ ∈ S_n = Equiv.Perm (Fin n)`, and `Des(σ) = {j | j+1<n and σ(j)>σ(j+1)}`. Put
`d = |Des(σ)|`. For `m : ℕ`, `CompatibleEulerianCuts σ m` consists of multisets `c : Sym
(Fin(n+1)) m` containing one copy of every element of `descentBoundaries σ`. These are weakly
ordered cut positions, with repetitions permitted.
