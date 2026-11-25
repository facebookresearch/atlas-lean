# Comp

For a functor `F` from a category `C` to monotone relations, morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of `C` and assertions `P`, `Q`, `R`: if the Hoare triple `{P} f {Q}` and the triple `{Q} g {R}` hold, then `{P} f ≫ g {R}` holds. Here a triple `{P} f {Q}` means that `F.map f` relates `P` to `Q`.
