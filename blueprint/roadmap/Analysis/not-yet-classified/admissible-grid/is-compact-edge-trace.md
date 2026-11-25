# Is Compact edge Trace

A canonical edge trace is a compact complex line segment.

```lean
theorem isCompact_edgeTrace (D : GridFilling) (e : GridEdge) :
    IsCompact (D.edgeTrace e)
```
