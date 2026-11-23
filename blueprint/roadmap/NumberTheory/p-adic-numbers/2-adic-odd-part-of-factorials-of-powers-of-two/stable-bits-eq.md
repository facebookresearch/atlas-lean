# Formula for the stable bits

Write $\operatorname{od}(n)$ for the odd part of a natural
number $n$. For all natural numbers $s$ and $d$, the stable bits are
$\operatorname{stab}(s, d) = \lfloor \operatorname{od}((2^{s+d-1})!) / 2^s \rfloor \bmod 2^d$,
where $s + d - 1$ is read as $0$ when $s = d = 0$.

For $s = e + 1$ the factorial is that of $2^{e+d}$, the shift is by $e + 1$ binary digits and the
modulus is $2^d$.

## Sources

- Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer Sequences 29 (2026), Article 26.3.1, Definition of stab.
