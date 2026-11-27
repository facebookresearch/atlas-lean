# Generalized Descartes rule and sign-change complexity of population size families

**Setting.** Under the coalescent with deterministic relative population size $\eta:\mathbb R_{\ge 0}\to\mathbb R_+$, pairs of lineages coalesce at rate $1/\eta(t)$. Let $R_\eta(t)=\int_0^t \eta(x)^{-1}dx$ and let $\widetilde\eta(\tau)=\eta(R_\eta^{-1}(\tau))$ be the size as a function of cumulative coalescence intensity. The expected time to the first coalescence among $m$ lineages is the Laplace transform of $\widetilde\eta$:

$$c_m = \mathbb{E}\bigl[T_{m,m}\bigr] = \int_0^\infty \widetilde\eta(\tau)\,e^{-\binom{m}{2}\tau}\,d\tau .$$

**Lemma 1.** The expected sample frequency spectrum of a sample of size $n$ determines $c_2,\dots,c_n$ up to a common positive factor.

**Sign changes.** For a piecewise-continuous $g$ on an interval, $\sigma(g)$ counts the points where $g$ changes sign, ignoring intervals where $g$ vanishes. The **sign-change complexity** of a family $\mathcal F$ of positive continuous size functions is

$$\mathcal S(\mathcal F) = \sup\bigl\{\sigma\bigl(\widetilde f_1(\cdot)-\widetilde f_2(\cdot-a)\bigr) : f_1,f_2\in\mathcal F,\ a\ge 0\bigr\},$$

and $\mathcal S(\mathcal M_K(\mathcal F))=\sup_{\eta_1,\eta_2}\sigma(\widetilde\eta_1-\widetilde\eta_2)$ for the family $\mathcal M_K(\mathcal F)$ of piecewise functions with at most $K$ pieces from $\mathcal F$ (pieces restarted at each change point, jumps allowed).

**Lemma 2.** $\mathcal S(\mathcal M_K(\mathcal F))\le (2K-2)+(2K-1)\,\mathcal S(\mathcal F)$, with equality for constant pieces, where $\mathcal S(\mathcal F_c)=0$.

**Theorem 4 (generalized Descartes rule of signs).** If $f:\mathbb R_{\ge 0}\to\mathbb R$ is piecewise continuous, not identically zero, and has finitely many sign changes, then

$$G(x)=\int_0^\infty f(t)\,e^{-tx}\,dt$$

has at most $\sigma(f)$ real roots counted with multiplicity.

**Theorem 5.** If $\mathcal S(\mathcal F)<\infty$ and $n\ge \mathcal S(\mathcal F)+2$, then $\eta\mapsto(c_2,\dots,c_n)$ is injective on $\mathcal F$.

**Theorem 6.** If $\mathcal S(\mathcal F)<\infty$ and $n\ge 2K+(2K-1)\,\mathcal S(\mathcal F)$, then $\eta\mapsto(c_2,\dots,c_n)$ is injective on $\mathcal M_K(\mathcal F)$. For constant pieces this is [identifiability of $K$-piece piecewise-constant histories from $n\ge 2K$](../size-fn-eq-of-first-coal-mean-eq.md).

The Myers–Fefferman–Patterson non-identifiable pair has a difference $\widetilde\eta_1-\widetilde\eta_2$ oscillating infinitely often near $\tau=0$, so it has infinite sign-change complexity and lies outside these theorems.

## Expansion

If two size functions give the same $c_2,\dots,c_n$, the Laplace transform $G$ of $f=\widetilde\eta_1-\widetilde\eta_2$ vanishes at the $n-1$ distinct points $x=\binom{m}{2}$, $2\le m\le n$. Theorem 4, adapted from Jameson's Laplace-transform version of Descartes' rule, allows at most $\sigma(f)\le\mathcal S$ roots, so $n-1>\mathcal S$ forces $f\equiv 0$; since $\eta$ is recovered from $\widetilde\eta$ through $S(t)=\int_0^t\widetilde\eta$, $\eta_1=\eta_2$. For piecewise families, two $K$-piece histories have at most $2K-1$ joint pieces in the $\tau$ scale, and the difference can change sign inside each joint piece at most $\mathcal S(\mathcal F)$ times and at each of the at most $2K-2$ joint breakpoints, which is Lemma 2. Theorem 4 and its proof are adapted from Jameson's Laplace-transform analogue of Descartes' rule (Lemma 4.5 there).

## Depends on

- [Expected time to the first coalescence](../first-coal-mean.md)
- [Bhaskar–Song identifiability](../size-fn-eq-of-first-coal-mean-eq.md)

## Sources

- A. Bhaskar and Y. S. Song, "Descartes' rule of signs and the identifiability of population demographic models from genomic variation data", Annals of Statistics 42 (2014), 2469–2493, <https://doi.org/10.1214/14-AOS1264>; preprint arXiv:1309.5056, <https://doi.org/10.48550/arXiv.1309.5056>, Section 2 (Lemmas 1–2, Definitions of sign changes and sign-change complexity, Theorems 3–6, discussion of the Myers–Fefferman–Patterson counterexample) and Section 3 (proofs).
