# Closure rectangle Of Box Interior

The closure of the open rectangle associated with a nondegenerate box is its closed carrier.

```lean
theorem closure_rectangleOfBoxInterior (I : BoxIntegral.Box (Fin 2)) :
    closure (rectangleOfBoxInterior I) = (rectangleOfBox I).carrier
```
