# Fubini Iso inv apply

Let `F : ℕ ⥤ ℕ ⥤ GrpCat`, `i j : ℕ`, and `a : (F.obj i).obj j`. The inverse map
sends the nested quotient representative at `(j, i)` for `F.flip` back to `(i, j)` for `F`,
with the same element `a`:

```text
(fubiniIso F).inv.hom (G.mk (innerColimitDiagram F.flip) ⟨j, G.mk (F.flip.obj j) ⟨i, a⟩⟩)
  = G.mk (innerColimitDiagram F) ⟨i, G.mk (F.obj i) ⟨j, a⟩⟩
```
