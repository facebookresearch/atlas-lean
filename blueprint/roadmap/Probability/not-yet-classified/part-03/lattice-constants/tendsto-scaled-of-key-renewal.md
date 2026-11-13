# Nonlattice constant identification

Let `Z t = z t + ∫ Z (t - y) dG(y)`
with Cramér root `∫ e^{θ y} dG = 1`. Assume the key renewal theorem for the
tilted law `G^θ = G.tilted (θ * ·)` (hypothesis `hKRT`): every solution `Y` of
`Y t = y t + ∫ Y (t - x) dG^θ(x)` with `(Y, y)` a `KeyRenewalAdmissible` pair
tends to `(∫_{(0,∞)} y) / mean(G^θ)`. This holds when `G^θ` is a nonlattice
probability law on `[0, ∞)` (Feller §XI.1) and is not proved here. If the
tilted pair `(e^{θ t} Z t, e^{θ t} z t)` is admissible, then
`e^{θ t} Z t → (∫_{(0,∞)} e^{θ s} z s ds) / ∫ y e^{θ y} dG(y)`,
i.e. `Z t ~ C e^{-θ t}` with this explicit `C`.
