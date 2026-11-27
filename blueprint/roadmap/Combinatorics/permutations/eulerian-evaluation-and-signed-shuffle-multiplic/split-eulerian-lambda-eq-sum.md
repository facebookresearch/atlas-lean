# The split evaluation coefficient formula

Let `p,q : ℕ`, `N=p+q`, and `Sh_(p,q) = ∑ s : Shuffle p q, sign(s.perm) [s.perm]` in `ℚ[S_N]`.
For `a : ℚ`, the split family is the sum over `α ∈ S_p`, `β ∈ S_q` with basis element
`[blockPermutation p q α β]` and coefficient `P_(p,d(α))(a) sign(α) * P_(q,d(β))(a) sign(β)`,
where `P_(r,d)(X)=(1/r!)∏_(j=0)^(r-1)(X+j-d)`.
