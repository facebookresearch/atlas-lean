# Counting $\ell$-free polynomials coprime to an irreducible

Let $F$ be a finite field with
$q$ elements, let $\ell \ge 2$ and let $d$ be a natural number. Call a monic polynomial over $F$
$\ell$-free if it is divisible by the $\ell$-th power of no monic irreducible polynomial. There is a
constant $C \ge 0$ such that for every monic irreducible polynomial $P$ over $F$ of degree $d$,
with $|P| = q^{d}$, and every natural number $n$, the number $N$ of $\ell$-free monic polynomials
of degree $n$ over $F$ that are coprime to $P$ satisfies

$$\left| N - \frac{q^n (1 - q^{1-\ell})(1 - |P|^{-1})}{1 - |P|^{-\ell}} \right| \le C.$$

So $C$ depends on $F$, $\ell$ and $d$ but not on $P$ or $n$.

The source states the lemma for $\ell > 0$. The factor $1 - q^{1-\ell}$ equals $1/\zeta_q(\ell)$,
where $\zeta_q(s) = 1/(1 - q^{1-s})$ is the zeta function of the polynomial ring over $F$; it has
a pole at $s = 1$, so the statement here assumes $\ell \ge 2$.

## Sources

- Juan Arévalo Gómez and Matilde Lalín, *Prime Factors with Given Multiplicity in h-Free and h-Full Polynomials over Function Fields*, INTEGERS 25 (2025), Article A9, Lemma 3.
