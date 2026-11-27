# Identifiability of piecewise-exponential demographies from the frequency spectrum

**Setting.** Let $\mathcal M_K(\mathcal F)$ be the population size histories with at most $K$ pieces, each piece $f_i(t-t_{i-1})$ on $[t_{i-1},t_i)$ taken from a family $\mathcal F$, as in the [sign-change complexity framework](generalized-descartes-rule-and-sign-change-complexity.md). Three families are considered: constant sizes $\mathcal F_c$ ($f(t)=\nu$), exponential sizes $\mathcal F_e$ ($f(t)=\nu e^{\beta t}$, $\beta\in\mathbb R$), and generalized-exponential sizes $\mathcal F_g$ solving $df/dt=\beta f^{\gamma}$, $f(0)=\nu$, with $\gamma\ge 0$ (super-exponential growth for $\gamma<1$). Let $c_m$ be the [expected time to the first coalescence](../first-coal-mean.md) among $m$ lineages.

**Corollaries 7–9.** The map $\eta\mapsto(c_2,\dots,c_n)$ is injective

- on $\mathcal M_K(\mathcal F_c)$ if $n\ge 2K$ ([Bhaskar–Song identifiability](../size-fn-eq-of-first-coal-mean-eq.md); tight, since this family has $2K-1$ positive parameters);
- on $\mathcal M_K(\mathcal F_e)$ if $n\ge 4K-1$;
- on $\mathcal M_K(\mathcal F_g)$ if $n\ge 6K-2$.

These follow from the general bound $n\ge 2K+(2K-1)\mathcal S(\mathcal F)$ with sign-change complexities $\mathcal S(\mathcal F_c)=0$, $\mathcal S(\mathcal F_e)\le 1$ and $\mathcal S(\mathcal F_g)\le 2$.

**Lemma 10 (scale).** If $n\ge 2K+(2K-1)\mathcal S(\mathcal F)$ and $\eta\in\mathcal M_K(\mathcal F)$ gives $(c_m)$, then for every $\kappa>0$ the unique model in $\mathcal M_K(\mathcal F)$ giving $(\kappa c_m)$ is $\zeta(t)=\kappa\,\eta(t/\kappa)$.

**Theorem 11 (unfolded SFS).** If $\mathcal S(\mathcal F)<\infty$ and $n\ge 2K+(2K-1)\mathcal S(\mathcal F)$, each expected sample frequency spectrum $(\xi_{n,1},\dots,\xi_{n,n-1})$ is consistent with exactly one equivalence class of models in $\mathcal M_K(\mathcal F)$, where models are equivalent when related by the rescaling of Lemma 10.

**Theorem 12 (folded SFS).** With the folded spectrum $\chi_{n,i}=(\xi_{n,i}+\xi_{n,n-i})/(1+\delta_{i,n-i})$, $1\le i\le\lfloor n/2\rfloor$, the same uniqueness holds whenever

$$n\ge 2(2K-1)\bigl(1+\mathcal S(\mathcal F)\bigr).$$

So for piecewise-exponential histories with $K$ epochs, a sample of $4K-1$ sequences already fixes the history up to the joint scaling of time and size from the unfolded spectrum, and $4(2K-1)$ sequences suffice from the folded one.

## Expansion

The expected spectrum determines the $c_m$ up to one common factor (Lemma 1), and that factor is exactly the time-and-size rescaling of Lemma 10. In the $\tau$ scale an exponential piece $\nu e^{\beta t}$ becomes $\widetilde f(\tau)=\nu/(1-\nu\beta\tau)$, whose reciprocal is affine, so the difference of two shifted exponential pieces has at most one zero and changes sign at most once; generalized-exponential pieces give at most two sign changes. Plugging these complexities into the [generalized Descartes bound](generalized-descartes-rule-and-sign-change-complexity.md) yields the three sample-size thresholds. Folding halves the number of observed coordinates, which roughly doubles the required sample size.

## Depends on

- [Generalized Descartes rule and sign-change complexity of population size families](generalized-descartes-rule-and-sign-change-complexity.md)
- [Expected time to the first coalescence](../first-coal-mean.md)
- [Bhaskar–Song identifiability](../size-fn-eq-of-first-coal-mean-eq.md)

## Sources

- A. Bhaskar and Y. S. Song, "Descartes' rule of signs and the identifiability of population demographic models from genomic variation data", Annals of Statistics 42 (2014), 2469–2493, <https://doi.org/10.1214/14-AOS1264>; preprint arXiv:1309.5056, <https://doi.org/10.48550/arXiv.1309.5056>, Section 2 (Corollaries 7–9, Lemma 10, Theorems 11–12, folded-spectrum definition) and Section 3 (proofs, including the sign-change complexities of the exponential and generalized-exponential families).
