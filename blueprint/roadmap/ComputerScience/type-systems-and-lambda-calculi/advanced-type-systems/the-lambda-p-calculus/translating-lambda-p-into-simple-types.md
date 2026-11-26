# Translating λP into simple types

In the presentation of [λP](the-calculus-lambda-p.md) without λ-abstractions in constructors, erase dependencies from types by $\overline{\alpha} = \alpha$, $\overline{(\forall x{:}\tau)\sigma} = \overline{\tau} \to \overline{\sigma}$ and $\overline{\varphi M} = \overline{\varphi}$, and translate both
types and terms of λP into simply typed terms, with a fixed type variable $0$ and fresh variables $x_\alpha$, $x_\tau$, $y$:

$$(\alpha M_1 \cdots M_n)^\bullet = x_\alpha\, M_1^\bullet \cdots M_n^\bullet, \quad ((\forall x{:}\tau)\sigma)^\bullet = x_\tau\, \tau^\bullet\, (\lambda x{:}\overline{\tau}.\, \sigma^\bullet),$$

$$x^\bullet = x, \quad (M\, N)^\bullet = M^\bullet\, N^\bullet, \quad (\lambda x{:}\tau.\, M)^\bullet = (\lambda y{:}0.\, \lambda x{:}\overline{\tau}.\, M^\bullet)\, \tau^\bullet.$$

Then, for some extension $\Gamma'$ of $\overline{\Gamma}$:

1. if $\Gamma \vdash \tau : *$ then $\Gamma' \vdash \tau^\bullet : 0$;
2. if $\Gamma \vdash M : \tau$ then $\Gamma' \vdash M^\bullet : \overline{\tau}$;
3. if $\Gamma \vdash M : \tau$ and $M \to_\beta M_1$, then $M^\bullet \twoheadrightarrow_\beta M_1^\bullet$ in at least one step.

So an infinite β-reduction in λP would give one in the simply typed λ-calculus, which yields [strong normalization of λP](strong-normalization-of-lambda-p.md).

## Depends on

- [The calculus λP](the-calculus-lambda-p.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 10.3, Definitions 10.3.1 and 10.3.2 and Lemma 10.3.3 (proof left as Exercise 10.7.2).
