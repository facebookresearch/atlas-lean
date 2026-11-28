# Logarithmic derivatives of $p$-torsion functions on curves over $\mathbb{F}_p$

On an elliptic curve over $\mathbb{F}_p$, sending a point $P$ of order dividing $p$ to $df_P/f_P$, where $\operatorname{div}(f_P)=p(P)-p(O)$, is a group homomorphism into differentials; for $P\ne O$ and $f_P$ normalized to start with $t^{-p}$, the constant term of its expansion at $O$ is the coefficient $f_1$ of $t^{-(p-1)}$ in $f_P$.

Let $p$ be a prime, $E$ an elliptic curve over $\mathbb{F}_p$, $t$ a uniformizer at $O$, and $\Omega_{\mathbb{F}_p}(E)$ the additive group of differentials on $E$. For $P\in E(\mathbb{F}_p)[p]$ let $f_P\in\mathbb{F}_p(E)^\times$ have divisor $p(P)-p(O)$; it is unique up to a nonzero constant, and for $P=O$ it is constant. Define $\lambda(P)=df_P/f_P$.

1. $\lambda(P)$ does not depend on the choice of $f_P$, and $\lambda:E(\mathbb{F}_p)[p]\to\Omega_{\mathbb{F}_p}(E)$ is a group homomorphism; $\lambda(O)=0$.
2. If $P\ne O$ and $f_P$ is scaled so that $f_P=t^{-p}+f_1t^{-(p-1)}+f_2t^{-(p-2)}+\cdots$, then $\lambda(P)=(f_1+\cdots)\,dt$.

Consequently, writing $c(P)$ for the constant term of the expansion of $\lambda(P)$ in powers of $t$ times $dt$, one has $c([a]P)=a\,c(P)$ in $\mathbb{F}_p$ for all $a\in\mathbb{Z}$.

## Depends on

- [Divisors on a curve](../../../../../AlgebraicGeometry/algebraic-curves/divisors-on-curves/divisors-on-a-curve/curve-divisor.md)
- [Order of an element at a place](../../../../../AlgebraicGeometry/algebraic-curves/divisors-on-curves/place/ord.md)

## Proof depends on

None.

## Expansion

Part 1 (Galbraith, Lemma 26.4.3): $d(cf)/(cf)=df/f$; for $Q=[a]P$ there is $g$ with $\operatorname{div}(g)=(Q)-a(P)+(a-1)(O)$, so $g^pf_P^a$ has divisor $p(Q)-p(O)$ and $d(g^pf_P^a)/(g^pf_P^a)=a\,df_P/f_P$ because $d(g^p)=pg^{p-1}dg=0$ in characteristic $p$. Part 2 (Lemma 26.4.5) differentiates the Laurent expansion, whose term $-pt^{-p-1}dt$ vanishes in characteristic $p$. On an anomalous curve ($\#E(\mathbb{F}_p)=p$) every rational point lies in $E(\mathbb{F}_p)[p]$, and this is the core of the Semaev–Satoh–Araki–Smart–Rück attack: turning it into an algorithm for the ECDLP needs $c(P)\ne0$ for $P\ne O$ and a bounded-precision computation of the expansion of $f_P$. Prerequisites still to add: principal divisors on $E$ and differentials with their expansions at a uniformizer.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Section 26.4.1, Lemma 26.4.3 and Lemma 26.4.5.
