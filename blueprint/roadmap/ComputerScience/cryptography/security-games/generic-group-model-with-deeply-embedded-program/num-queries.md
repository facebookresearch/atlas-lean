# Worst-case query count of a generic-group program

The static query bound of a generic-group program: `ret` issues none, `mul`
and `inv` issue one query plus the continuation's count, and `eqTest` takes
the maximum over its two branches.
