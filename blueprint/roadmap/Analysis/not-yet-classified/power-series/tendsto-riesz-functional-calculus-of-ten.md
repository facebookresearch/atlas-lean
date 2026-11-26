# Tendsto riesz Functional Calculus of tendsto Locally Uniformly On

On one common open neighborhood of the spectrum, locally uniform
convergence of analytic scalar representatives implies norm convergence of
their Riesz functional-calculus values.

Here `A` is a complete unital complex normed algebra with its given norm. Multiplication need not
commute; the zero algebra remains allowed.

```lean
theorem tendsto_rieszFunctionalCalculus_of_tendstoLocallyUniformlyOn
    {ι : Type uι} {l : Filter ι}
    (a : A) {G : Set ℂ} (hG : IsOpen G)
    (hσG : spectrum ℂ a ⊆ G) {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ i, DifferentiableOn ℂ (F i) G)
    (hf : DifferentiableOn ℂ f G)
    (hconv : TendstoLocallyUniformlyOn F f l G) :
    Tendsto
      (fun i ↦ rieszFunctionalCalculus a
        (HolomorphicNearSpectrum.ofFunction a (F i)
          (((hF i).analyticOnNhd hG).mono hσG)))
      l
      (𝓝 (rieszFunctionalCalculus a
        (HolomorphicNearSpectrum.ofFunction a f
          ((hf.analyticOnNhd hG).mono hσG))))
```
