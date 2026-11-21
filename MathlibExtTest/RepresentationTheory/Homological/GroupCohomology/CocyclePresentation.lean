module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CocyclePresentation

open groupCohomology

/-- Consumer with the original binders. -/
theorem exactSource
    {G M P : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
    [AddCommGroup P] [SMul G P]
    (Fn Fn₁ : Subgroup M) (hstab : ∀ (g : G) (x : M), x ∈ Fn → g • x ∈ Fn)
    (π : M → P) (hπmul : ∀ x y, x ∈ Fn → y ∈ Fn → π (x * y) = π x + π y)
    (hπsurj : ∀ p : P, ∃ x ∈ Fn, π x = p)
    (hπker : ∀ x, x ∈ Fn → (π x = 0 ↔ x ∈ Fn₁))
    (hπsmul : ∀ (g : G) (x : M), x ∈ Fn → π (g • x) = g • π x)
    (hP : ∀ f : G → P, IsCocycle₁ f → IsCoboundary₁ f)
    (f : G → M) (hfF : ∀ g, f g ∈ Fn) (hf : IsMulCocycle₁ f) :
    ∃ a ∈ Fn, ∀ g, f g / (g • a / a) ∈ Fn₁ :=
  groupCohomology.exists_div_mem_of_isMulCocycle₁_of_presentation
    Fn Fn₁ hstab π hπmul hπsurj hπker hπsmul hP f hfF hf

/-- Higher-universe consumer. -/
theorem exactSourceUniverse.{u, v, w}
    {G : Type u} {M : Type v} {P : Type w} [Group G] [CommGroup M]
    [MulDistribMulAction G M] [AddCommGroup P] [SMul G P]
    (Fn Fn₁ : Subgroup M) (hstab : ∀ (g : G) (x : M), x ∈ Fn → g • x ∈ Fn)
    (π : M → P) (hπmul : ∀ x y, x ∈ Fn → y ∈ Fn → π (x * y) = π x + π y)
    (hπsurj : ∀ p : P, ∃ x ∈ Fn, π x = p)
    (hπker : ∀ x, x ∈ Fn → (π x = 0 ↔ x ∈ Fn₁))
    (hπsmul : ∀ (g : G) (x : M), x ∈ Fn → π (g • x) = g • π x)
    (hP : ∀ f : G → P, IsCocycle₁ f → IsCoboundary₁ f)
    (f : G → M) (hfF : ∀ g, f g ∈ Fn) (hf : IsMulCocycle₁ f) :
    ∃ a ∈ Fn, ∀ g, f g / (g • a / a) ∈ Fn₁ :=
  groupCohomology.exists_div_mem_of_isMulCocycle₁_of_presentation
    Fn Fn₁ hstab π hπmul hπsurj hπker hπsmul hP f hfF hf
