# Common Overlay filling Supported In

The difference cycle is filled by signed rectangles with closed carriers in the closure of the
multiplicity-difference support.

```lean
theorem commonOverlay_fillingSupportedIn (D E : GridFilling) :
    (D.commonOverlay E).toCycle.FillingSupportedIn
      (closure (D.multiplicityDifferenceSupport E))
```
