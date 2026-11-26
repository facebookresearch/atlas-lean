# Cell Box injective

Different integer indices give different half-open cell boxes at a fixed positive scale.

```lean
theorem cellBox_injective (D : GridFilling) : Function.Injective D.cellBox
```
