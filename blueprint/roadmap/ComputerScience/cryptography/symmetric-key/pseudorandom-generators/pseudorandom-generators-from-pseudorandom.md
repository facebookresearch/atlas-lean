# Pseudorandom generators from pseudorandom functions

Let $K$, $X$, $Y$ and $R$ be finite sets with $K$, $Y$ and $R$ nonempty, let
$F : K \to X \to Y$ be a keyed function, let $x_1, \dots, x_n \in X$ be distinct, and let
$G : K \to Y^n$ be the generator $G(k) = (F(k, x_1), \dots, F(k, x_n))$. Let $A$ be a
distinguisher for strings in $Y^n$ whose coins are uniform on $R$, and let $B$ be the PRF
distinguisher with coins in $R$ that, with coins $r$ and oracle $O : X \to Y$, queries $O$ at
$x_1, \dots, x_n$, in this order, and outputs the guess of $A$ on $(O(x_1), \dots, O(x_n))$ with
coins $r$. Then:

- for all coins $r$ and every oracle $O$, $B$ asks exactly the $n$ queries $x_1, \dots, x_n$, in
  this order, and outputs the guess of $A$ on $(O(x_1), \dots, O(x_n))$ with coins $r$;
- the PRG advantage of $A$ against $G$ equals the PRF advantage of $B$ against $F$:
  $\mathrm{Adv}^{\mathrm{PRG}}[A, G] = \mathrm{Adv}^{\mathrm{PRF}}[B, F]$.

There is no model of running time. Boneh and Shoup ask that $B$ be an *elementary wrapper* around
$A$, so that its running time is about that of $A$; here this is the form of $B$, which besides its
$n$ queries runs $A$ once, on the answers, with $A$'s own coins. PRF distinguishers draw their
coins uniformly from a finite set and $B$ uses $A$'s coins as its own, which is why $A$'s coins are
taken uniform, as a probabilistic algorithm's are. An equality needs some such hypothesis: PRG
distinguishers may have coins with any distribution, so a PRG advantage can be irrational, whereas
every PRF advantage is rational.

With the oracle $F(k, \cdot)$ for a uniform key $k$, $B$ shows $A$ the string $G(k)$, so the two
real worlds agree. With a uniformly random function $f : X \to Y$, $B$ shows $A$ the string
$(f(x_1), \dots, f(x_n))$, which is uniform on $Y^n$ because the points $x_i$ are distinct, so the
two random worlds agree too.

The equality needs no relation between $|K|$ and $|Y|^n$. The condition $|K| < |Y|^n$ only makes
$G$ expand its seed, which [asymptotic PRG security](prgsecure.md) requires, following Katz and
Lindell; it is a hypothesis of the asymptotic form,
[Asymptotic PRG security from a PRF](prg-secure-prg-of-prf.md). It does not come from Boneh and
Shoup: their Theorem 4.8 has no such hypothesis, and their Definition 3.1 of a secure PRG does not
require expansion.

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, [Section 4.4.4, Theorem 4.8, and Section 3.1.1, Definition 3.1](https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_4.pdf)
