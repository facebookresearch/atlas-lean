# A CPS translation of λΔ

Translate implicational formulas by $k(\alpha) = \neg\neg\alpha$, $k(\bot) = \neg\neg\bot$ and $k(\varphi \to \psi) = \neg\neg(k(\varphi) \to k(\psi))$, and [λΔ-terms](the-lambda-delta-calculus.md)
into λ-terms by

$$t(x) = \lambda k.\, x\, k, \quad t(\lambda x.\, M) = \lambda k.\, k\, (\lambda x.\, t(M)), \quad t(M\, N) = \lambda k.\, t(M)\, (\lambda m.\, m\, t(N)\, k),$$

$$t(\Delta x.\, M) = \lambda k.\, (\lambda x.\, t(M))\, (\lambda h.\, h\, (\lambda j.\, \lambda i.\, i\, (j\, k)))\, (\lambda z.\, z).$$

If $\Gamma \vdash M : \varphi$ in the simply typed λΔ-calculus, then $k(\Gamma) \vdash t(M) : k(\varphi)$ in the simply typed λ-calculus. Hence no closed term of the simply typed λΔ-calculus has
type $\bot$: a closed $M : \bot$ would give the closed simply typed term $t(M)\, (\lambda z.\, z) : \bot$.

## Depends on

- [The λΔ-calculus](the-lambda-delta-calculus.md)
- [Simple type assignment à la Curry](../../simply-typed-lambda-calculus/decision-problems-for-simple-types/simple-type-assignment-a-la-curry.md)

## Proof depends on

- [No closed term of a base type](../../normalization-of-the-simply-typed-lambda-calculu/no-closed-base.md): with $\bot$ as the base type, the translation of a closed inhabitant of $\bot$ would be a closed simply typed term of type $\bot$

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 8.6, Definitions 8.6.1 and 8.6.2 and Propositions 8.6.3 and 8.6.4.
