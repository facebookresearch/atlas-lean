# Decomposition and dichotomy for martingale densities

Let $\mu$ be a finite measure and $\nu$ a probability measure on
$(\Omega,\mathcal F)$, with increasing sigma-fields $\mathcal F_n$
generating $\mathcal F$. Assume
$\mu|_{\mathcal F_n}\ll\nu|_{\mathcal F_n}$ and choose nonnegative
Radon--Nikodym densities $X_n$. Set $X=\limsup_nX_n$ with values in
$[0,\infty]$. Then $X_n$ is a $\nu$-martingale and converges $\nu$-almost
surely to the finite value $X$, and the measure decomposition is

$$\mu=X\nu+\mathbf1_{\{X=\infty\}}\mu.$$

Consequently

$$\mu\ll\nu\ \Longleftrightarrow\ X<\infty\ \mu\text{-a.e.}
 \ \Longleftrightarrow\ \int X\,d\nu=\mu(\Omega),$$

and

$$\mu\perp\nu\ \Longleftrightarrow\ X=\infty\ \mu\text{-a.e.}
 \ \Longleftrightarrow\ \int X\,d\nu=0.$$

The lemma permits a mixture of absolutely continuous and singular parts;
it does not assert that every such pair of measures is in one of the two
extreme cases.
In particular, if $P,Q$ are probabilities on
$\mathcal F=\sigma(\bigcup_n\mathcal F_n)$ and
$Q|_{\mathcal F_n}=W_nP|_{\mathcal F_n}$ with $\mathbb E_PW_n=1$, then
finite $Q$-almost-sure $\limsup W_n$ implies $\mathbb E_PW=1$, while
infinite $Q$-almost-sure $\limsup W_n$ implies $W=0$ $P$-almost surely.
Here $W=\lim W_n$ only $P$-almost surely; the globally defined limsup is
what is evaluated under $Q$.

## Proof depends on

- [Martingale almost-sure convergence](../../martingales/martingale-convergence-theorems/exists-ae-tendsto-of-pos-part-bdd-2.md)
- [The Lp martingale convergence theorem](../../martingales/martingale-convergence-theorems/tendsto-e-lp-norm-limit-process-of-e-lp.md)
- [Strong law for indicator sums](../../laws-of-large-numbers/strong-law-of-large-numbers/pairwise-independent-events/pairwise-indep-slln.md)

## Expansion

Put $C=\mu(\Omega)+1$ and $\rho=(\mu+\nu)/C$. The restricted densities
$U_n=d\mu_n/d\rho_n$ and $V_n=d\nu_n/d\rho_n$ satisfy
$U_n+V_n=C$, so both are bounded martingales under $\rho$.
L2 convergence gives limits $U,V$. On each finite-level measurable set
the integral identity passes to the limit. Uniqueness of finite measures
on the generating algebra then gives $\mu=U\rho$, $\nu=V\rho$, and
$U+V=C$ almost surely. Local absolute continuity implies $V_n>0$
$\rho$-almost surely and $X_n=U_n/V_n$. On $\{V>0\}$ the limit is
$U/V$; on $\{V=0\}$ it is infinity, because $U=C>0$.
Splitting those two sets proves the displayed decomposition and the two
chains of equivalences, including $\mu=0$.

For a concrete product-martingale example, under $P$ let independent
factors take values $1/2,3/2$ with probabilities $1/2,1/2$, and put
$W_n$ equal to their product. Under $Q$ their probabilities are $1/4,3/4$.
The finite-coordinate likelihood ratio is $W_n$, but the strong law for
the indicator of the larger factor gives log-growth rates
$\tfrac12\log(3/4)<0$ under $P$ and
$\tfrac14\log(27/16)>0$ under $Q$.
Thus $W_n\to0$ under $P$ and $W_n\to\infty$ under $Q$.

## Sources

- R. Lyons and Y. Peres, *Probability on Trees and Networks*, corrected edition of August 19, 2026, <https://rdlyons.pages.iu.edu/prbtree/book.pdf>, Section 12.2, Lemma 12.2 and decomposition (12.4). The bounded common-reference-density proof and explicit two-point example above make the measure changes precise.
