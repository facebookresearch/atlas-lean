# Horseshoe Middle XIso

The middle object iso: unop of the projective coordinates, `unop` pushed
through the biproduct, then swapped into `(I₁ ⊞ I₃)` order.

Informal sketch: `(H.middle.complex.X n).unop ≅ unop (op I₃.X n ⊞ op I₁.X n)`
(unop'd `ProjectiveResolution.horseshoe_middle_X_iso`) `≅ unop (op I₃.X n) ⊞ unop (op I₁.X n)`
(`unopBiprodIso`) `= I₃.X n ⊞ I₁.X n` (definitionally) `≅ I₁.X n ⊞ I₃.X n`
(`biprod.braiding'`).
