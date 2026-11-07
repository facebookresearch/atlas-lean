# Sharpness of the phase transition

**Sharpness of the phase transition** for Bernoulli bond percolation on `ℤ^d`, `d ≥ 1`
(Duminil-Copin–Tassion 2016; Aizenman–Barsky 1987; Menshikov 1986):

1. `p̃_c = p_c`;
2. for every `p ∈ tildePcSet d` (a finite `S ∋ 0` has `φ_p(S) < 1`),
   `ℙ_p(0 ↔ ℤ^d \ Λ_{n-1}) ≤ C e^{-cn}` for some `c, C > 0`;
3. `θ(q) ≥ (q - p̃_c)/(q(1 - p̃_c))` for `p̃_c < q < 1`.

Scope of the items:
* Item 2 is stated on `tildePcSet d`, not on `[0, p_c)`: passing from `p < p̃_c` to
  `p ∈ tildePcSet d` needs monotonicity of `p ↦ φ_p(S)`, and passing from `p < p_c` to `θ(p) = 0`
  needs monotonicity of `θ`; neither is proved in MathlibExt (θ monotonicity is
  `theta_mono_parameter` in PhyslibExt `RandomCluster/PcUpperViaFK`).
* Item 3 is informative only when `p̃_c < 1`. This file does not prove that for any `d`; at `d = 1`
  it fails (`p̃_c = p_c = 1`) and item 3 is vacuous. For `d = 2`, `p_c < 1` is proved in PhyslibExt
  (`StatMech.Percolation.pc_two_lt_one_via_fk`), which with item 1 makes item 3 non-vacuous
  there.
