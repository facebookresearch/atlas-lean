# A CPS translation of λΔ

Translate implicational formulas by $k(\alpha) = \neg\neg\alpha$, $k(\bot) = \neg\neg\bot$ and $k(\varphi \to \psi) = \neg\neg(k(\varphi) \to k(\psi))$, and [λΔ-terms](the-lambda-delta-calculus.md)
into λ-terms by

$$t(x) = \lambda k.\, x\, k, \quad t(\lambda x.\, M) = \lambda k.\, k\, (\lambda x.\, t(M)), \quad t(M\, N) = \lambda k.\, t(M)\, (\lambda m.\, m\, t(N)\, k),$$

$$t(\Delta x.\, M) = \lambda k.\, (\lambda x.\, t(M))\, (\lambda h.\, h\, (\lambda j.\, \lambda i.\, i\, (j\, k)))\, (\lambda z.\, z).$$

If $\Gamma \vdash M : \varphi$ in the simply typed λΔ-calculus, then $k(\Gamma) \vdash t(M) : k(\varphi)$ in the simply typed λ-calculus. Hence classical implicational logic embeds
in intuitionistic implicational logic, and is consistent: a closed $M : \bot$ would give the closed term $t(M)\, (\lambda z.\, z) : \bot$.

## Depends on

- [The λΔ-calculus](the-lambda-delta-calculus.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 8.6, Definitions 8.6.1 and 8.6.2 and Propositions 8.6.3 and 8.6.4.
