# Duhamel hypotheses for a product-integral map

**Duhamel hypotheses for a product-integral map** `P : E → F` with Duhamel operator
`Ψ : E → E → (E →L[ℝ] F)` on the domain `D`, with uniform bound `C` and continuity class `S`.

This is the minimal restatement, as a hypothesis, of the properties of the Lebesgue–Stieltjes
product integral `P A t = ∏_{(0, t]} (1 + dA)` (constructed in the separate task T77, not imported
here) that the Hadamard-differentiability argument uses. For that product integral on integrators
of total variation `≤ M`, `Ψ A B h t = ∫_{(0, t]} P(A)(0, s) dh(s) P(B)(s, t]` and:
* `duhamel` is the **Duhamel equation** (Gill–Johansen 1990);
* `norm_le` is the **sup-norm bound** obtained from integration by parts, with `C` depending only
  on `M` (Gill–Johansen 1990);
* `tendsto` is the continuity of the Duhamel integral in the second integrator, proved classically
  for step functions `s` (whose uniform closure contains the continuous functions).
