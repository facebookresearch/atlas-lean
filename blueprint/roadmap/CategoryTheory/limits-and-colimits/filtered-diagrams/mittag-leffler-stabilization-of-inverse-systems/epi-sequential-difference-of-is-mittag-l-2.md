# Mittag–Leffler towers have surjective sequential difference

Let `R : Type u` be a ring and `A : ℕᵒᵖ ⥤ ModuleCat.{w} R` satisfy
`A.IsSequentialMittagLeffler`: for each term `A_n`, the images of later terms in `A_n`
eventually stabilize. Then the sequential difference `D : ∏ A_n → ∏ A_n`,
`D(a)_n=a_n-τ_n(a_{n+1})`, is an epimorphism, where `τ_n : A_{n+1} → A_n` is the successor
map.
