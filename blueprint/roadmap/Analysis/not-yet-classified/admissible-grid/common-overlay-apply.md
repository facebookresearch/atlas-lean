# Common Overlay apply

The signed overlay coefficient is the first refined indicator minus the second.

```lean
theorem commonOverlay_apply (D E : GridFilling)
    (I : BoxIntegral.Box (Fin 2)) :
    D.commonOverlay E I =
      prepartitionIndicator (D.leftOverlayPrepartition E) I -
        prepartitionIndicator (D.rightOverlayPrepartition E) I
```
