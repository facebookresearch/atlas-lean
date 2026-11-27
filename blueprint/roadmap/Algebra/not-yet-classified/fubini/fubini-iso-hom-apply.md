# Fubini Iso hom apply

Let `F : ℕ ⥤ ℕ ⥤ GrpCat`, `i j : ℕ`, and `a : (F.obj i).obj j`. The forward map
sends the nested quotient representative at `(i, j)` to the one at `(j, i)` for `F.flip`,
with the same element `a`:

```text
(fubiniIso F).hom.hom (G.mk (innerColimitDiagram F) ⟨i, G.mk (F.obj i) ⟨j, a⟩⟩)
  = G.mk (innerColimitDiagram F.flip) ⟨j, G.mk (F.flip.obj j) ⟨i, a⟩⟩
```
