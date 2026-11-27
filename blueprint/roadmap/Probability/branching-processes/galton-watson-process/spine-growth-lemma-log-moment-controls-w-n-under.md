# The logarithmic offspring moment controls size-biased tree growth

Let $1<m=\mathbb EL<\infty$ and let $Q_*$ be the
[size-biased marked-tree law](size-biased-galton-watson-measure-and-spine-deco.md),
with tree projection $Q$. On every tree set
$W_n=Z_n/m^n$ and $\overline W=\limsup_nW_n$ as an extended nonnegative
value. With the convention $0\log^+0=0$:

- if $\mathbb E[L\log^+L]<\infty$, then $W_n$ converges to a finite limit
  $Q$-almost surely;
- if $\mathbb E[L\log^+L]=\infty$, then $\limsup_nW_n=\infty$
  $Q$-almost surely.

The exact size-bias identity, including infinite expectations, is

$$\mathbb E\log\widehat L=m^{-1}\mathbb E[L\log^+L].$$

For $Y=\widehat L-1$, this is finite if and only if
$\mathbb E\log^+Y<\infty$: for integers $k\ge2$,
$\log(k-1)\le\log k\le\log(k-1)+\log2$, and $k=1$ contributes zero
under the stated convention.

## Depends on

- [Size-biased tree and off-spine immigration](size-biased-galton-watson-measure-and-spine-deco.md)

## Proof depends on

- [First Borel--Cantelli lemma](../../foundations/borel-cantelli-lemmas/first-borel-cantelli-lemma/measure-limsup-at-top-eq-zero.md)
- [Second Borel--Cantelli lemma](../../foundations/borel-cantelli-lemmas/second-borel-cantelli-lemma/measure-limsup-eq-one.md)
- [Nonnegative martingale convergence](../../martingales/martingale-convergence-theorems/exists-ae-tendsto-of-pos-part-bdd-2.md)

## Expansion

For iid nonnegative $X_n$ with common law $X$, the tail integral test gives
$\sum_n\mathbb P(X>\epsilon n)<\infty$ for each $\epsilon>0$ when
$\mathbb EX<\infty$. First Borel--Cantelli and countably many rational
$\epsilon$ imply $X_n/n\to0$ almost surely.
If $\mathbb EX=\infty$, the same tail sum diverges for every positive
threshold slope. Independence and second Borel--Cantelli give
$\limsup X_n/n=\infty$ almost surely.

Let $I_n=Z_n-1$ be the off-spine immigration process under $Q_*$, starting
with $I_0=0$. Condition on the entire immigration sequence $Y=(Y_k)$.
It is independent of the ordinary offspring arrays. In the finite-log
case, apply the preceding tail argument to $\log^+Y_k$: for a sufficiently
small $\epsilon>0$ with $e^\epsilon<m$, eventually $Y_k\le e^{\epsilon k}$,
so $S=\sum_{k\ge1}Y_k/m^k<\infty$ almost surely. Conditional on such a
sequence, the process

$$R_n=I_n/m^n+\sum_{k>n}Y_k/m^k$$

is a nonnegative martingale for the off-spine reproduction filtration,
with expectation $S$. This follows by conditioning the recurrence
$I_{n+1}=\sum_{i=1}^{I_n}L_{n,i}+Y_{n+1}$.
Martingale convergence gives a finite limit for $R_n$. Its deterministic
tail term tends to zero, hence $I_n/m^n$ and
$W_n=I_n/m^n+m^{-n}$ converge finitely. This supplies the conditional
convergence argument; bounded expectations alone would not control a
sequence's limsup without its martingale structure.

In the infinite-log case, for every integer $a>\log m$ there are infinitely
many $n$ with $Y_n>e^{an}$, almost surely. Since $I_n\ge Y_n$, the limsup
of $W_n$ is infinite. The countable conditional construction uses ordinary
product laws and Fubini, not an unconditional finite mean for immigration.
Finally, summing $\log k\cdot kp_k/m$ proves the size-bias identity by
nonnegative summation.

## Sources

- R. Lyons and Y. Peres, *Probability on Trees and Networks*, corrected edition of August 19, 2026, <https://rdlyons.pages.iu.edu/prbtree/book.pdf>, Lemma 12.1, Exercise 12.2, the size-bias identity and Theorem 12.3 (Seneta's immigration theorem). The compensated conditional martingale $R_n$ writes out the finite-growth argument using only a martingale, avoiding an unstated submartingale prerequisite.
