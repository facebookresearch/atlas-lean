# Assembly of local generator data over nested covers

Let `C : Type u₁` have morphism universe `v₁`, `J` be a topology, and `R : Sheaf J
RingCat.{u}`, with additive sheafification and the locally-bijective comparison on first and
second slices. For `M`, a cover `X : I → C` with `I : Type u₁`, and data `D_i :
LocalGeneratorsData.{max u₁ v₁}(M.over(X i))`, `bind M X hX D` is local generator data for `M`
at universe `max u₁ v₁`. Its charts are indexed by pairs `(i,j)` with `j∈D_i.I`, and the chart
object is `(D_i.X j).left`.
