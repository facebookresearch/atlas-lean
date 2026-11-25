# Double counting when exactly one value of a coordinate leaves a set

Let `ι` be a finite index set and `β_j`, for `j ∈ ι`, finite sets, and consider the functions `f`
assigning to each `j` an element `f(j) ∈ β_j`. Fix an index `i` and two properties `A` and `E` of
such functions such that:

- `A` does not depend on coordinate `i`: replacing `f(i)` by any `x ∈ β_i` does not change
  whether `f` has property `A`;
- every function with property `E` has property `A`;
- for every function `f` with property `A`, exactly one `x ∈ β_i` is such that the function
  obtained from `f` by replacing `f(i)` with `x` does not have property `E`.

Then `#E · |β_i| + #A = #A · |β_i|`, where `#A` and `#E` are the numbers of functions with
properties `A` and `E`; that is, `#A = (#A - #E) · |β_i|`, where `#A - #E` counts the functions
with property `A` but not `E`.
