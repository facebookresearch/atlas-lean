# The continuous-time (Lebesgue–Stieltjes) product integral on `ℓ^∞((0, τ))`, restated as a hypothesis

**The continuous-time (Lebesgue–Stieltjes) product integral on `ℓ^∞([0, τ])`, restated as a
hypothesis.** `P A t` stands for `∏_{(0, t]} (1 + dA)` and `Ψ A B` for the Duhamel operator
`h ↦ (t ↦ ∫_{(0, t]} P(A)(0, s) dh(s) P(B)(s, t])` on the domain `D` (a total-variation ball, where
the construction of the separate task T77 applies). Besides the Duhamel hypotheses of
`IsDuhamelProductIntegral`:
* `continuous_subset_closure`: the continuity class `S` of the Duhamel operator is uniformly dense
  in `C[0, τ]` (classically, `S` = step functions);
* `pureJump`: the **definition of the product integral on pure-jump integrators**: if
  `A t = ∑_{s_j ≤ t} a j` on `[0, τ]` with jump times `0 < s 0 < s 1 < ⋯`, then
  `P A t = ∏_{s_j ≤ t} (1 + a j)`.

`Ψ A B` is a continuous linear operator on all of `ℓ^∞([0, τ])`: the Stieltjes integral defines it
on bounded-variation `h`, the integration-by-parts bound extends it to their uniform closure (the
regulated functions), and any norm-preserving extension beyond that (one exists because
`ℓ^∞([0, τ])` is an injective Banach space) satisfies these fields; the theorems only evaluate
`Ψ A B` on `B - A`, on `S`, and on limits of elements of `S`.

Nothing here constructs `P`; theorems taking `IsStieltjesProductIntegral τ P Ψ D S C` are
conditional on the product integral of T77 satisfying it.
