# Ultraweak operator convergence along a filter

Let `H` be a complex normed
inner-product space, with no completeness assumption. Write `ℓ²(H)=lp (fun _ : ℕ => H) 2`
for its square-summable vector sequences. For `x,y ∈ ℓ²(H)`, put `ω_(x,y)(T)=Σ_n ⟨y_n,T
x_n⟩`. for any filter `l` on an index type, `OperatorUltraweak.Tendsto T_i l T` means
`T_i→T` along `l` in the coefficient topology on `B(H)`.
