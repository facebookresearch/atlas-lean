# Is Closed edge Trace

A canonical edge trace is closed in the complex plane.

```lean
theorem isClosed_edgeTrace (D : GridFilling) (e : GridEdge) :
    IsClosed (D.edgeTrace e)
```
