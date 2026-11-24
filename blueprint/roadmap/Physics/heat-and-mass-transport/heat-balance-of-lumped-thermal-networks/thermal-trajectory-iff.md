# State-space form of the zone thermal network

**State-space form of the zone thermal network** (trajectory correspondence, and the
physical-to-canonical bridge). Let `C i > 0` in every zone. The curve `s ↦ fun i => T i s` is
a trajectory of the plant `(thermalA C G g0, thermalB C g0)` driven by the input
`s ↦ Sum.elim (fun _ => Tout s) (fun i => P i s)` if and only if, at every time `t` and in
every zone `i`, `T i` has a derivative `Tv` at `t` with
`C i * Tv = (∑ j, G i j * (T j t - T i t)) + g0 i * (Tout t - T i t) + P i t`. Then `Tv` is
the derivative of `T i` at `t`, so the right side says that `T` solves the zone equations
with boundary input `g0 i * (Tout - T i)` and heating power `P i`. For the owner record `S`
that `StateSpaceCoeffs.ofMatrix` builds from the four pinned matrices, the inline trajectory
condition on the owner record (the convention of
`MathlibExt.Analysis.Control.IsControllableOn`; the record itself carries no trajectory
semantics), `∀ t, HasDerivAt z (S.A (z t) + S.B (w t)) t` for `z = fun s i => T i s` and
`w = fun s => Sum.elim (fun _ => Tout s) (fun i => P i s)`, reduces to the left side by
`simp only [ofMatrix_A_apply, ofMatrix_B_apply]`. Physical domain `C i > 0`,
`G i j = G j i ≥ 0`, `g0 i ≥ 0` (positive thermal resistances `1 / G i j` and `1 / g0 i`
where a path exists); the equivalence holds for all real `G` and `g0`.
