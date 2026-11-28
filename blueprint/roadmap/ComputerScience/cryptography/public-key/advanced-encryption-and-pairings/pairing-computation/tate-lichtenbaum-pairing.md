# Tate–Lichtenbaum pairing

For an elliptic curve over a finite field $F$ with $Q$ elements and $n\mid Q-1$, the Tate–Lichtenbaum (Frey–Rück) pairing sends $P\in E(F)[n]$ and the class of $R$ in $E(F)/nE(F)$ to $\hat t_n(P,R)=f(D_R)^{(Q-1)/n}\in\mu_n$, where $\operatorname{div}(f)=nD_P$ and $D_P,D_R$ are Galois-fixed divisors representing $P,R$ with disjoint supports.

Let $F$ be a finite field with $Q$ elements, $\overline F$ an algebraic closure, $E$ an elliptic curve over $F$, and $n\ge1$ with $n\mid Q-1$. Divisors below are divisors on $E$ over $\overline F$ that are fixed by $\operatorname{Gal}(\overline F/F)$; their points may be defined only over extensions of $F$. For $P\in E(F)[n]$ and $R\in E(F)$ choose such divisors $D_P\sim(P)-(O)$ and $D_R\sim(R)-(O)$ with disjoint supports, and $f\in F(E)^\times$ with $\operatorname{div}(f)=nD_P$. With $f(D_R)=\prod_Xf(X)^{n_X}$ for $D_R=\sum_Xn_X(X)$, which lies in $F^\times$ because $D_R$ and $f$ are Galois-fixed, the *reduced Tate–Lichtenbaum pairing* is

$$
\hat t_n(P,R)=f(D_R)^{(Q-1)/n}\in\mu_n .
$$

Its value depends only on $P$ and on $R+nE(F)$, giving

$$
\hat t_n:E(F)[n]\times E(F)/nE(F)\longrightarrow\mu_n .
$$

Equivalently, the unreduced pairing $t_n(P,R)=f(D_R)\cdot(F^\times)^n\in F^\times/(F^\times)^n$ is well defined, and $z\mapsto z^{(Q-1)/n}$ is an isomorphism $F^\times/(F^\times)^n\to\mu_n$. One may take $D_P=(P)-(O)$, so that $f$ is the Miller function $f_{n,P}$ up to a constant; then $D_R$ must avoid the support of $(P)-(O)$, which is $\{O,P\}$ for $P\ne O$ and empty for $P=O$ (where $f$ is constant and the value is $1$), and for $P\ne O$ a choice $D_R=(R+S)-(S)$ with $S$ rational need not exist, for instance on $y^2=x^3+2x^2+2$ over $\mathbb{F}_3$, whose rational points are $O$ and $P=(2,0)$, with $n=2$ and $R=P$, where both rational points are excluded. For a curve over $\mathbb{F}_q$ and $n$ prime to $q$, one takes $F=\mathbb{F}_{q^k}$ with $k=k(q,n)$ the embedding degree, so that $n\mid Q-1$.

## Depends on

- [Miller functions](miller-functions.md)
- [Embedding degree](../embedding-degree-and-pairing-attacks/embedding-degree.md)
- [Evaluation of a divisor against a function](../../../../../AlgebraicGeometry/algebraic-curves/divisors-on-curves/evaluation-of-curve-divisors/eval.md)
- [Quotient group](../../../../../GroupTheory/group-basics/quotient-group.md)
- [Group homomorphisms](../../../../../GroupTheory/semigroups-and-monoids/group-homomorphism.md)

## Proof depends on

None.

## Expansion

Independence of the choices, following Galbraith's Lemma 26.3.2: changing $D_R$ within its class by a Galois-fixed principal divisor $\operatorname{div}(h)$ with support disjoint from $D_P$ multiplies $f(D_R)$ by $f(\operatorname{div}h)=h(\operatorname{div}f)=h(D_P)^n$, an $n$-th power, by Weil reciprocity. Changing $D_P$ to $D_P+\operatorname{div}(g)$ replaces $f$ by $cfg^n$, so $f(D_R)$ is multiplied by $c^{\deg D_R}g(D_R)^n=g(D_R)^n$, once $D_R$ avoids the supports of both representatives of $P$; to compare two arbitrary choices, first move $D_R$ within its class off the union of all supports involved and apply both comparisons. Replacing $R$ by $R+[n]R'$ changes $D_R$ by $n$ times a Galois-fixed degree-zero divisor representing $R'$, chosen with support disjoint from $D_P$, plus a principal divisor. Scaling $f$ by $c$ multiplies $f(D_R)$ by $c^{\deg D_R}=1$. Prerequisites still to add: the moving lemma that every Galois-fixed degree-zero divisor class contains Galois-fixed representatives avoiding any given finite set; descent showing that a Galois-fixed principal divisor is the divisor of a function over $F$; the Abel–Jacobi identification of $E(\overline F)$ with degree-zero divisor classes; and Weil reciprocity for divisors whose points are defined over extensions of $F$.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Section 26.3, equation (26.2), Lemma 26.3.2 with its footnotes, and Section 26.3.2.
- P. Bruin, "The Tate pairing for Abelian varieties over finite fields", *Journal de Théorie des Nombres de Bordeaux* 23(2):323–328, 2011, doi:10.5802/jtnb.764; numbering from the author's version, <http://pub.math.leidenuniv.nl/~bruinpj/tate-pairing.pdf>, Section 1 (the Frey–Rück pairing for $n\mid\#k-1$).
