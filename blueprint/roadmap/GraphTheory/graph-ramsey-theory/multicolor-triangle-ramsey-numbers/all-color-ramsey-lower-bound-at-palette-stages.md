# All-color Ramsey lower bound from palette stages

For every integer $k\ge K(3)$ there is an integer $H\ge3$ such that $K(H)\le k<K(H+1)$ and $R_k(3)\ge(H/e^{38})^k$ in the reals. Here

$$K(H)=H\max(2,\lceil\log H\rceil)(w(w+1)+1),\qquad w=\lceil2H\log H\rceil.$$

This is a bound for all color counts above the first eligible stage, not just for the sequence $K(H)$.

## Depends on

- [Multicolor triangle Ramsey number](multicolor-triangle-ramsey-number.md)

## Proof depends on

- [Ramsey lower bound from a recursive palette construction](recursive-palette-ramsey-lower-bound.md)

## Expansion

Bracket $k$ between consecutive palette counts using growth and monotonicity of $K$. For $H\ge3$ and $a=\max(2,\lceil\log H\rceil)$, prove the scaled adjacent bound $aK(H+1)\le(a+34)K(H)$, then the exponential comparison from $(H/e^4)^{K(H)}$ to $(H/e^{38})^k$. Transfer the stage estimate by monotonicity of the Ramsey number in the number of allowed colors. The coloring construction supplies the bound at $K(H)$ through the linked prerequisite; it is not used to define the theorem's quantities.

## Sources

- [Staged bound and conversion to all color counts](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L2556-L2584)
