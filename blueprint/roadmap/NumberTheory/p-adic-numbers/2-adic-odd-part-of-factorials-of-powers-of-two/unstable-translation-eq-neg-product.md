# The unstable translation constant equals $-zw$

Write $\operatorname{od}(n)$ for the odd part
of a natural number $n$, $(2^e-1)!!$ for the product of the odd numbers from $1$ to $2^e-1$,
$\operatorname{uns}(e,d) = \lfloor \operatorname{od}((2^e)!)/2^{e+1} \rfloor \bmod 2^d$ and
$\operatorname{stab}(e+1,d) = \lfloor \operatorname{od}((2^{e+d})!)/2^{e+1} \rfloor \bmod 2^d$.
Let $K$, $z$ and $w$ be $2$-adic integers such that, with congruences in $\mathbb{Z}_2$,
$\operatorname{uns}(e,d) + K \equiv \operatorname{stab}(e+1,d) \pmod{2^d}$ for all natural
numbers $d < e$, $z \equiv \operatorname{od}((2^{e-1})!) \pmod{2^e}$ for all $e \ge 1$, and
$w \equiv \lfloor ((2^e-1)!! - 1)/2^e \rfloor \pmod{2^{e-1}}$ for all $e \ge 3$. Then $K = -zw$.

The three hypotheses are the defining properties of $K$ (Theorem 1), $z$ (Corollary 8) and $w$
(the definition after Corollary 10).

## Sources

- Donald M. Davis, *Some 2-adic Integers Related to the Odd Part of 2^e!*, Journal of Integer Sequences 29 (2026), Article 26.3.1, Theorem 14.
