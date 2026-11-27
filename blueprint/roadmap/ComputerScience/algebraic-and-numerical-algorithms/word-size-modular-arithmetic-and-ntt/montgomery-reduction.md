# Montgomery reduction

Montgomery reduction computes $TR^{-1}\bmod m$, for an auxiliary modulus $R$ coprime to $m$, using a multiplication modulo $R$ to form $U$, the integer product $Um$, an addition and an exact division by $R$; the result lies in $[0,2m)$, within one subtraction of the reduced residue.

Let $m\ge 1$ and $R\ge 1$ be integers with $\gcd(m,R)=1$, let $m'=-m^{-1}\bmod R$ (so $mm'\equiv-1\pmod R$ and $0\le m'<R$), and let $T$ be an integer with $0\le T<mR$. Put $U=Tm'\bmod R$, with $0\le U<R$. Then:

1. $(T+Um)/R$ is an integer;
2. $(T+Um)/R\equiv TR^{-1}\pmod m$;
3. $0\le (T+Um)/R<2m$, so $(T+Um)/R$ equals either $TR^{-1}\bmod m$ or $(TR^{-1}\bmod m)+m$.

If $R=b^{n}$ with $n\ge 1$ is a power of the radix $b$, the hypothesis $\gcd(m,R)=1$ is equivalent to $\gcd(m,b)=1$ (for $b$ a power of two: $m$ odd), and reduction modulo $R$ and division by $R$ become digit truncation and shifts.

## Depends on

None.

## Proof depends on

None.

## Expansion

HAC's justification: write $U=Tm'+\kappa R$ and $m'm=-1+\ell R$ with integers $\kappa,\ell$; then $(T+Um)/R=\ell T+\kappa m$ is an integer, and since $T+Um\equiv T\pmod m$ it is congruent to $TR^{-1}$. Note 14.30(i) gives the bound from $T<mR$ and $U<R$.

## Sources

- Alfred J. Menezes, Paul C. van Oorschot, Scott A. Vanstone, *Handbook of Applied Cryptography*, CRC Press (1996), Chapter 14, §14.3.2: Fact 14.29 (Montgomery reduction) with its justification, and Note 14.30(i)–(ii); chapter copy distributed with the publisher's permission at [cacr.uwaterloo.ca/hac](https://cacr.uwaterloo.ca/hac/about/chap14.pdf).
- Peter L. Montgomery, "Modular Multiplication Without Trial Division", Mathematics of Computation 44(170) (1985), 519–521, DOI [10.1090/S0025-5718-1985-0777282-X](https://doi.org/10.1090/S0025-5718-1985-0777282-X) (original reference).
