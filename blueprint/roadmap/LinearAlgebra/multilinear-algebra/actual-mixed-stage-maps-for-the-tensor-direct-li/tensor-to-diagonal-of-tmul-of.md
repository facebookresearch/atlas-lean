# Return tensor comparison on mixed stage classes

Let R be a commutative semiring, ι a preorder with decidable
equality, and M_a, N_a R-modules with additive commutative monoid structures.
Let f_ab : M_a → M_b and g_ab : N_a → N_b be R-linear transitions
for a ≤ b. Write D for their simultaneous tensor direct-limit module.
Assume both transition families satisfy identity and composition.
Assume also that ι is directed.
The return map has pure mixed-stage value
[x]_a ⊗ [y]_b ↦ stage_(a,b)(x ⊗ y)
= [f_ac(x) ⊗ g_bc(y)]_c for any c ≥ a, b.
