# Generalized Descartes rule and sign-change complexity of population size families

**Setting.** Under the coalescent with deterministic relative population size $\eta:\mathbb R_{\ge 0}\to\mathbb R_+$, pairs of lineages coalesce at rate $1/\eta(t)$. Let $R_\eta(t)=\int_0^t \eta(x)^{-1}dx$ and let $\widetilde\eta(\tau)=\eta(R_\eta^{-1}(\tau))$ be the size as a function of cumulative coalescence intensity. The expected time to the first coalescence among $m$ lineages is the Laplace transform of $\widetilde\eta$:

$$c_m = \mathbb{E}\bigl[T_{m,m}\bigr] = \int_0^\infty \widetilde\eta(\tau)\,e^{-\binom{m}{2}\tau}\,d\tau .$$

**Lemma 1.** The expected sample frequency spectrum of a sample of size $n$ determines $c_2,\dots,c_n$ up to a common positive factor.

For a right-continuous function $g : [a, \infty) \to \mathbb{R}$, let $\sigma(g)$ denote its sign-variation count, the supremum of the $k \ge 0$ for which there exist $a \le t_0 < t_1 < \dots < t_k$ with $g(t_{i-1}) g(t_i) < 0$ for all $1 \le i \le k$ (for $a = 0$ this is the count of the Laplace sign-variation bound page linked below). The sign-change complexity of a family $\mathcal F$ of positive continuous size functions $f$ with $\widetilde f(\tau) \le M_f e^{c_f \tau}$ for some constants $M_f$ and $c_f < 1$ is

$$\mathcal S(\mathcal F) = \sup\bigl\{\sigma\bigl(\widetilde f_1(\cdot)-\widetilde f_2(\cdot-a)\bigr) : f_1,f_2\in\mathcal F,\ a\ge 0\bigr\},$$

and $\mathcal S(\mathcal M_K(\mathcal F))=\sup_{\eta_1,\eta_2}\sigma(\widetilde\eta_1-\widetilde\eta_2)$ for the family $\mathcal M_K(\mathcal F)$ of histories with at most $K$ pieces from $\mathcal F$: for some $k \le K$, change points $0=t_0<t_1<\dots<t_{k-1}<t_k=\infty$ and $f_1,\dots,f_k\in\mathcal F$, $\eta(t)=f_i(t-t_{i-1})$ on $[t_{i-1},t_i)$, so jumps are allowed and $\eta$ takes the right-hand value at each change point. Each $\widetilde f$ is continuous, so the differences in $\mathcal S(\mathcal F)$ are continuous on $[a,\infty)$; members $\eta$ of $\mathcal M_K(\mathcal F)$ and their $\widetilde\eta$ are right-continuous and piecewise continuous, and $\widetilde\eta$ has exponential order $c_{f_k}<1$, since it is bounded on $[0,R_\eta(t_{k-1}))$ and equals $\widetilde f_k(\tau-R_\eta(t_{k-1}))$ after.

**Lemma 2.** $\mathcal S(\mathcal M_K(\mathcal F))\le (2K-2)+(2K-1)\,\mathcal S(\mathcal F)$, with equality for constant pieces, where $\mathcal S(\mathcal F_c)=0$.

**Theorem 5.** If $\mathcal S(\mathcal F)<\infty$ and $n\ge \mathcal S(\mathcal F)+2$, then $\eta\mapsto(c_2,\dots,c_n)$ is injective on $\mathcal F$.

**Theorem 6.** If $\mathcal S(\mathcal F)<\infty$ and $n\ge 2K+(2K-1)\,\mathcal S(\mathcal F)$, then $\eta\mapsto(c_2,\dots,c_n)$ is injective on $\mathcal M_K(\mathcal F)$. For constant pieces this is [identifiability of $K$-piece piecewise-constant histories from $n\ge 2K$](../size-fn-eq-of-first-coal-mean-eq.md). Theorems 5 and 6 are a variant of Bhaskar and Song's Theorems 5 and 6: they use the alternation count $\sigma$ and the exponential-order hypothesis of the linked Laplace sign-variation bound in place of the sign-change count of Bhaskar and Song's Definition 3.

The Myers–Fefferman–Patterson non-identifiable pair has a difference $\widetilde\eta_1-\widetilde\eta_2$ oscillating infinitely often near $\tau=0$, so it has infinite sign-change complexity and lies outside these theorems.

## Proof depends on

- [Sign-variation bound for Laplace transforms](../../../../Analysis/harmonic-analysis/integral-transforms/laplace-transform/sign-variation-bound-for-laplace-transforms.md)

## Expansion

If two size functions $\eta_1,\eta_2$, both in $\mathcal F$ or both in $\mathcal M_K(\mathcal F)$, give the same $c_2,\dots,c_n$, let $f=\widetilde\eta_1-\widetilde\eta_2$. It is right-continuous and piecewise continuous, it has exponential order $c<1$ (the larger of the two orders), and $\sigma(f)\le\mathcal S$, where $\mathcal S$ is $\mathcal S(\mathcal F)$ (take $a=0$) or $\mathcal S(\mathcal M_K(\mathcal F))$. Its Laplace transform $G$ vanishes at the $n-1$ distinct points $x=\binom{m}{2}$, $2\le m\le n$, which all lie in $(c,\infty)$ because $\binom{m}{2}\ge 1>c$. If $f\not\equiv 0$, the Laplace sign-variation bound allows at most $\sigma(f)\le\mathcal S$ zeros of $G$ in $(c,\infty)$, so $n-1>\mathcal S$ forces $f\equiv 0$; since $\eta$ is recovered from $\widetilde\eta$ through $S(t)=\int_0^t\widetilde\eta$, $\eta_1=\eta_2$. For piecewise families, two $K$-piece histories have at most $2K-1$ joint pieces in the $\tau$ scale, and the difference can change sign inside each joint piece at most $\mathcal S(\mathcal F)$ times and at each of the at most $2K-2$ joint breakpoints, which is Lemma 2. Bhaskar and Song state that their Theorem 4 and its proof are adapted from Jameson's Laplace-transform analogue of Descartes' rule (Lemma 4.5 there); the linked bound is a variant of their Theorem 4.

## Depends on

- [Expected time to the first coalescence](../first-coal-mean.md)
- [Bhaskar–Song identifiability](../size-fn-eq-of-first-coal-mean-eq.md)

## Sources

- A. Bhaskar and Y. S. Song, "Descartes' rule of signs and the identifiability of population demographic models from genomic variation data", Annals of Statistics 42 (2014), 2469–2493, <https://doi.org/10.1214/14-AOS1264>; preprint arXiv:1309.5056, <https://doi.org/10.48550/arXiv.1309.5056>, Section 2 (Lemmas 1–2, Definitions of sign changes and sign-change complexity, Theorems 3–6, discussion of the Myers–Fefferman–Patterson counterexample) and Section 3 (proofs).
