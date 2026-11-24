# Sortslice Reverse safe

`sortslice_reverse` is adequate and safe on every valid half-open range.
The optional second physical phase is controlled by the explicit C-pointer
mode, never inferred from an individual entry.

The `n = 0` case is an intentional totalization of the Lean model: CPython's
body decrements its exclusive high pointer before testing it, while every
reviewed C call site supplies a positive length.  Consequently the empty-range
case proved here is a model-domain extension, not a claim about executing the C
body on a zero-length range.
