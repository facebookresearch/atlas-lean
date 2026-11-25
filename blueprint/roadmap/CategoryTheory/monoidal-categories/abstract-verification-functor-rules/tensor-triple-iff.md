# Tensor Triple iff

For a morphism `f : X ⊗ U ⟶ Y ⊗ V` and pairs of assertions `P` and `Q`, the tensor triple `{P} f {Q}` holds if and only if there are assertions `P'` and `Q'` such that the tensor comparison of `F` relates `P` to `P'`, the Hoare triple `{P'} f {Q'}` holds, and the inverse comparison relates `Q'` to `Q`.
