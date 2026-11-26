# The alternating finite-length sum of Tor modules

For a commutative ring R, M,N ∈ ModuleCat.{u} R, and h : FiniteTorData R M N, define
χ_Tor(h)=Σ_{j∈range(h.cutoff)}(-1)^j·(length_R Tor_j(M,N)).toNat in ℤ. Finiteness below the
cutoff makes these guarded natural lengths valid, and an empty cutoff gives the empty sum.
