# Chosen Pi Pi Hom naturality

General naturality/extensionality criterion for `chosenPiPiHom` at the raw
dependent-product level, oriented for direct source-indexed specialization.

We are given source and target nested families

* `X : (i : I) → K i → C` with independently chosen inner, outer, and flat products,
* `Y : (i' : I') → K' i' → C` with independently chosen inner, outer, and flat products,

outer and fiber equivalences `eI : I ≃ I'` and `eK : ∀ i, K i ≃ K' (eI i)`,
component morphisms `f i j : X i j ⟶ Y (eI i) (eK i j)`,
and arbitrary comparison maps

* `flatMap : ∏ᶜ (flat X) ⟶ ∏ᶜ (flat Y)`,
* `iterMap : ∏ᶜ (iter X) ⟶ ∏ᶜ (iter Y)`,

with projection hypotheses indexed by source `i j`:

* `flatMap ≫ π_Y ⟨eI i, eK i j⟩ = π_X ⟨i, j⟩ ≫ f i j`,
* `iterMap ≫ π_Y (eI i) ≫ π_Y (eK i j) = π_X i ≫ π_X j ≫ f i j`.

Then `flatMap ≫ chosenPiPiHom_Y = chosenPiPiHom_X ≫ iterMap`.

The source-oriented orientation `I ≃ I'` and `K i ≃ K' (eI i)` is chosen so that
applications whose components are naturally indexed by source positions `i j`
specialize without transports: the hypotheses `hFlat` and `hIter` already use
source indices `i j` on both sides. The proof uses two `Pi.hom_ext`
applications followed by surjectivity of `eI` and `eK` to reduce an arbitrary
target pair `i' j'` to a source pair `i j`. We reuse `chosenPiPiHom_π_π`
projection lemmas and `Pi.hom_ext`.
