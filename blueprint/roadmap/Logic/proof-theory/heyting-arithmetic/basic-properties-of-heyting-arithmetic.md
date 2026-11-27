# Basic properties of Heyting arithmetic

In [Heyting arithmetic](heyting-arithmetic.md):

1. equality is decidable: $\mathrm{HA} \vdash \forall x\, \forall y\, (x = y \vee \neg (x = y))$;
2. (existence property) if $\mathrm{HA} \vdash \exists x\, \varphi(x)$ for a closed formula $\exists x\, \varphi(x)$, then $\mathrm{HA} \vdash \varphi(\underline{k})$ for some $k \in \mathbb{N}$;
3. $\mathrm{HA} \vdash (\varphi \vee \psi) \leftrightarrow \exists x\, ((x = 0 \to \varphi) \wedge (\neg (x = 0) \to \psi))$ for a variable $x$ not free in $\varphi$ or $\psi$;
4. (disjunction property) if $\mathrm{HA} \vdash \varphi \vee \psi$ for closed $\varphi$ and $\psi$, then $\mathrm{HA} \vdash \varphi$ or $\mathrm{HA} \vdash \psi$;
5. (Markov's principle as a rule) if $\mathrm{HA} \vdash \forall x\, (\varphi(x) \vee \neg \varphi(x))$ and $\mathrm{HA} \vdash \neg\neg \exists x\, \varphi(x)$, then $\mathrm{HA} \vdash \exists x\, \varphi(x)$.

## Depends on

- [Heyting arithmetic](heyting-arithmetic.md)

## Expansion

This page becomes ready once:

- A proof source for the existence property, such as the Kripke-model proof that the lecture notes below cite to D. van Dalen, checked (source check)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Theorem 11.4.1 and its proof sketch (the existence property is cited there without proof).
