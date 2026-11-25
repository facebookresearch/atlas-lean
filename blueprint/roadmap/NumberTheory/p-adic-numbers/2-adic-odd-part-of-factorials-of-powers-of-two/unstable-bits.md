# Unstable bits

Write $\operatorname{od}(n)$ for the odd part of a natural number $n$. For
natural numbers $e$ and $d$, the unstable bits $\operatorname{uns}(e,d)$ are the natural number
$\lfloor \operatorname{od}((2^e)!) / 2^{e+1} \rfloor \bmod 2^d$, whose binary digits are the $d$
bits of $\operatorname{od}((2^e)!)$ at positions $e+1, \dots, e+d$ (position $0$ being the least
significant bit).

The paper assumes $e > d$ only when stating Theorem 1, so the definition itself is total.

## Sources

- Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer Sequences 29 (2026), Article 26.3.1, Definition of uns.
