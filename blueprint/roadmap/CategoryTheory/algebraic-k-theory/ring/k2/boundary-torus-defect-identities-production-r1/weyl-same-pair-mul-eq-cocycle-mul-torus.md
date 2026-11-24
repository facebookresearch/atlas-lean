# Weyl same Pair mul eq cocycle mul torus

Same-pair Weyl product modulo the torus cocycle.

Hypotheses: `[Field F]`, distinct indices `i ≠ j` (`hij`), units `p q : Fˣ`.

Exact orientation: `weyl i j p * weyl i j q = c * torus i j ((-p) * q⁻¹)`
with the cocycle defect `c ∈ torusCocycleSubgroup` exhibited on the left.

Purpose: supplies the mixed Weyl/torus transport step that rewrites an
arbitrary same-pair Weyl product as a left central defect times a torus word;
downstream conjugation then moves torus words across Weyl words.

Nonclaims: no defect triviality (`c = 1` is false in general), no Weyl
conjugation theorem, no ordered torus normal form, no `C ≤ H`, no TWT
closure, no kernel generation, and no Matsumoto comparison or isomorphism.
