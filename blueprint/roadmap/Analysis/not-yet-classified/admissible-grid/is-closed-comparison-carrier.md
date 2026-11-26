# Is Closed comparison Carrier

The comparison carrier of two fillings is closed.

```lean
theorem isClosed_comparisonCarrier (D E : GridFilling) :
    IsClosed (D.comparisonCarrier E)
```
