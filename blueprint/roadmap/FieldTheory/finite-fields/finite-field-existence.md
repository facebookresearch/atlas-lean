# The Galois field with pⁿ elements

For every prime $p$ and every integer $n \ge 1$ there is a field with exactly $p^n$ elements. Mathlib gives an explicit witness: for a prime $p$ and a natural number $n$, it defines $\mathrm{GaloisField}\,p\,n$ to be Mathlib's splitting field of the polynomial $X^{p^n} - X$ over the field $\mathbb{Z}/p\mathbb{Z}$, and equips it with the structure of a finite field of characteristic $p$ that is an algebra over $\mathbb{Z}/p\mathbb{Z}$; for $n \ge 1$ this is the Galois field $\operatorname{GF}(p^n)$. The theorem states that if $n \neq 0$, then $\mathrm{GaloisField}\,p\,n$ has exactly $p^n$ elements, that is, its cardinality is $p^n$.

## Sources

- Kenneth Ireland and Michael Rosen, A Classical Introduction to Modern Number Theory, 2nd ed., Graduate Texts in Mathematics 84, Springer-Verlag, 1990.
- David S. Dummit and Richard M. Foote, Abstract Algebra, 3rd ed., John Wiley & Sons, 2004.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the Galois field as the splitting field of X^(p^n) − X over ZMod p, with its field, characteristic, algebra and finiteness structures: `GaloisField`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/FieldTheory/Finite/GaloisField.lean#L62-L71.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the number of elements of the Galois field when n ≠ 0: `GaloisField.card`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/FieldTheory/Finite/GaloisField.lean#L116.
