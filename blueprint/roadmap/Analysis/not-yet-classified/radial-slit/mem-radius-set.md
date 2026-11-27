# Membership in the finite radius union

Let `n : ℕ` and `E : RadialSlitData n` have
real endpoints `a_i=E.inner i`, `b_i=E.outer i` for `i∈Fin n`, with `0≤a_i≤b_i≤1`. Put
`R=⋃_{i∈Fin n}[a_i,b_i]`, `S={z∈ℂ | Re z∈R ∧ Im z=0}` and `D={z∈ℂ | ‖z‖<1}∖S`. For `r∈ℝ`,
`r∈E.radiusSet ↔ ∃i∈Fin n, a_i≤r≤b_i`. No disjointness or positive interval length is
assumed.
