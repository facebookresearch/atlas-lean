# Sectionwise exterior power of the relative Kähler presheaf

For `f : X ⟶ Spec A` and a
degree `d` chosen by the caller, the sectionwise `d`-th exterior power of the presheaf
`kaehlerPresheaf`. Its sheafification is not `topDifferentials d` by definition, since
`topDifferentials d` sheafifies the exterior power of the sheaf `kaehler`; `topToSectionsₗ` sends
its sections to sections of `topDifferentials d`.
