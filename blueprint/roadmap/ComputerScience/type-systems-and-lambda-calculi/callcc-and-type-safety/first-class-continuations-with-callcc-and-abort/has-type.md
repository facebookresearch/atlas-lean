# Typing judgment of the calculus with callcc

For an answer type `T`, the judgment
`HasType T Γ e A`, where the context `Γ` lists the types of the free de Bruijn variables (index
`0` first), is the least relation closed under the rules of the simply typed λ-calculus with
natural numbers (multiplication of two numbers is a number; the zero test takes a number and two
branches of a common type) and two rules for control: if `e` has type `(A → B) → A`, then
`callcc e` has type `A` (Wright and Felleisen, §6.2); if `e` has the answer type `T`, then
`abort e` has every type (Wright and Felleisen, Figure 7, with the single answer type `T`).
