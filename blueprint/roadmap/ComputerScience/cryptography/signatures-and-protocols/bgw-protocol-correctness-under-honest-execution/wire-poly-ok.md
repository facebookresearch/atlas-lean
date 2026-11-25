# Every wire polynomial shares its trace value

Let `F` be a field and `Party` a finite type of parties, with Shamir
parameters `params` and a straight-line program `prog` over the arithmetic
signature. Suppose every input polynomial satisfies `(inPolys k).eval 0 = x k`
and `(inPolys k).natDegree ≤ params.threshold`, and every gate polynomial
satisfies `(P g).eval 0 = (prog.eval arithInterp x) g` and `(P g).natDegree ≤
params.threshold`. Then every wire polynomial, input or gate, evaluates at `0`
to the wire's trace value on `x` and has natural degree at most
`params.threshold`.
