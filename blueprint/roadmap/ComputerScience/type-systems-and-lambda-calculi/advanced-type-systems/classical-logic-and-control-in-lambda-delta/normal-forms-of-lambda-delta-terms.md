# Normal forms of λΔ-terms

Let $\mathcal{N}$ be the least class of [λΔ-terms](the-lambda-delta-calculus.md) such that $\lambda x_1 \dots x_n.\, \Delta y_1 \dots \Delta y_m.\, z\, M_1 \cdots M_k \in \mathcal{N}$ whenever
$M_1, \dots, M_k \in \mathcal{N}$, for $n, m, k \ge 0$ and any variable $z$. If $\Gamma \vdash M : \varphi$ in the simply typed λΔ-calculus and $M$ is a $\beta\Delta$-normal form, then
$M \in \mathcal{N}$: a normal term makes assumptions, decomposes them by eliminations, applies double-negation elimination, and then builds up by introductions.
With strong normalization of $\to_{\beta\Delta}$ on typable terms, it follows that no closed term has type $\bot$.

## Depends on

- [The λΔ-calculus](the-lambda-delta-calculus.md)

## Proof depends on

- [Strong normalization of λΔ via a CPS translation](strong-normalization-of-lambda-delta-via-a-cps.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Section 8.4, Definition 8.4.4, Proposition 8.4.5 and Corollary 8.4.6.
