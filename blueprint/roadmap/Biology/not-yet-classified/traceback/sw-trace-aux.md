# Local traceback from a cell

The local traceback from cell `(i, j)` of the table `T` with
fuel `n`: stop at a cell equal to `0` or on the border and return its position and the emitted
columns; otherwise step as in `nwTraceAux`, in constant time per step.
