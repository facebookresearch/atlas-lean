# Exists open eq On rep

Every scalar representative of the given germ agrees with the chosen representative on some
open neighborhood of the spectrum.

Here `A` is a unital complex normed algebra with its given norm. Multiplication need not commute;
no nonzero-algebra hypothesis is imposed.

```lean
theorem HolomorphicNearSpectrum.exists_open_eqOn_rep
    (a : A) (f : HolomorphicNearSpectrum a) (g : ℂ → ℂ)
    (hg : (g : SpectrumGerm a) = f.1) :
    ∃ U : Set ℂ, IsOpen U ∧ spectrum ℂ a ⊆ U ∧ Set.EqOn (f.rep a) g U
```
