# MOV/Frey–Rück reduction of the ECDLP to a finite field

The reduced Tate–Lichtenbaum pairing over $\mathbb{F}_{q^k}$ transfers the discrete logarithm problem in a subgroup of prime order $r$ of $E(\mathbb{F}_q)$ to the discrete logarithm problem in the order-$r$ subgroup of $\mathbb{F}_{q^k}^*$, where $k$ is the embedding degree: for a suitable $R$, $Q\mapsto\hat t_r(Q,R)$ is an isomorphism onto $\mu_r$.

Let $E$ be an elliptic curve over $\mathbb{F}_q$, let $r$ be a prime with $r\mid\#E(\mathbb{F}_q)$ and $r\nmid q$, let $k=k(q,r)$ be the embedding degree, and let

$$
\hat t_r : E(\mathbb{F}_{q^k})[r]\times E(\mathbb{F}_{q^k})/rE(\mathbb{F}_{q^k})\longrightarrow \mu_r\subseteq\mathbb{F}_{q^k}^*
$$

be the reduced Tate–Lichtenbaum pairing of $E$ over $\mathbb{F}_{q^k}$, which is defined since $r\mid q^k-1$. Let $P\in E(\mathbb{F}_q)$ have order $r$. Then:

1. For every $R\in E(\mathbb{F}_{q^k})$ the map $\langle P\rangle\to\mu_r$, $Q\mapsto\hat t_r(Q,R)$, is a group homomorphism.
2. The map $R\mapsto \hat t_r(P,R)$ is a surjective homomorphism $E(\mathbb{F}_{q^k})\to\mu_r$; in particular there is $R\in E(\mathbb{F}_{q^k})$ with $z=\hat t_r(P,R)\ne1$.
3. If $z\ne1$ then $z$ generates $\mu_r$ and, for every $a\in\mathbb{Z}$, $\hat t_r([a]P,R)=z^a$. So $Q\mapsto\hat t_r(Q,R)$ is an isomorphism $\langle P\rangle\to\mu_r$, and the discrete logarithm of $Q$ to base $P$ equals, modulo $r$, the discrete logarithm of $\hat t_r(Q,R)$ to base $z$ in $\mathbb{F}_{q^k}^*$.

Thus an ECDLP instance in $\langle P\rangle$ is solved by one discrete logarithm in the order-$r$ subgroup of $\mathbb{F}_{q^k}^*$, once an $R$ with $\hat t_r(P,R)\ne1$ is known and $\hat t_r(Q,R)$ is evaluated. When $q$ is a proper prime power, $\mathbb{F}_{q^k}$ is an ambient target field, not necessarily the smallest field of characteristic $\operatorname{char}\mathbb{F}_q$ containing $\mu_r$.

## Depends on

- [Elliptic-curve discrete logarithm problem](../elliptic-curve-discrete-logarithm-problem.md)
- [Embedding degree](../../advanced-encryption-and-pairings/embedding-degree-and-pairing-attacks/embedding-degree.md)
- [Tate–Lichtenbaum pairing](../../advanced-encryption-and-pairings/pairing-computation/tate-lichtenbaum-pairing.md)
- [Discrete-logarithm experiment](../../hardness-assumptions/dlog-game.md)
- [Group homomorphisms](../../../../../GroupTheory/semigroups-and-monoids/group-homomorphism.md)

## Proof depends on

- [The reduced Tate–Lichtenbaum pairing is perfect](../../advanced-encryption-and-pairings/pairing-computation/reduced-tate-pairing-is-perfect.md)

## Expansion

Part 1 is linearity in the first argument. For part 2, linearity in the second argument makes $R\mapsto\hat t_r(P,R)$ a homomorphism, and perfectness with $P\ne O$ gives an $R$ with $\hat t_r(P,R)\ne1$; a nontrivial homomorphism to a group of prime order $r$ is surjective. Part 3 follows from part 1. Calculation of the cost of finding $R$: the fibers of $R\mapsto\hat t_r(P,R)$ have equal size, so for $R$ uniform in $E(\mathbb{F}_{q^k})$ the value differs from $1$ with probability exactly $1-1/r$. With fresh independent uniform trials, one pairing evaluation per trial and one further evaluation on $Q$ after the first success, the expected number of pairing evaluations of that procedure is $r/(r-1)+1$. This counts pairing evaluations only, assumes an exact uniform sampler, and is not claimed to be optimal; it is derived here, not taken from the cited sources. Evaluating the pairing with Miller's algorithm on divisors with rational support is not always possible: on $y^2=x^3+2x^2+2$ over $\mathbb{F}_3$, with $r=2$ and $k=1$, the rational points are $O$ and $P=(2,0)$, and with $D_P=(P)-(O)$ no rational point is left for a shifted divisor representing $R=P$; a general evaluator needs divisors with points over extensions of $\mathbb{F}_{q^k}$ and arithmetic in those extensions. Menezes, Okamoto and Vanstone used the Weil pairing; Frey and Rück used the Tate–Lichtenbaum pairing, which needs only $E(\mathbb{F}_{q^k})$. For prime fields, the SEC 1 domain-parameter rules require $p^B\not\equiv1\pmod n$ for $1\le B<100$ to exclude small embedding degree.

## Sources

- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Section 26.4 (the MOV/FR reduction).
- P. Bruin, "The Tate pairing for Abelian varieties over finite fields", *Journal de Théorie des Nombres de Bordeaux* 23(2):323–328, 2011, doi:10.5802/jtnb.764; numbering from the author's version, <http://pub.math.leidenuniv.nl/~bruinpj/tate-pairing.pdf>, Section 4 (perfectness of the Frey–Rück pairing).
- A. V. Sutherland, *18.783 Elliptic Curves*, Lecture 23 notes, MIT, Fall 2023, <https://math.mit.edu/classes/18.783/2023/LectureNotes23.pdf>, Sections 23.6–23.7.
- Certicom Research, *SEC 1: Elliptic Curve Cryptography*, Standards for Efficient Cryptography, version 2.0, 2009, <https://www.secg.org/sec1-v2.pdf>, Sections 3.1.1.1 and 3.1.1.2.1 (the prime-field condition $p^B\not\equiv1\pmod n$ for $1\le B<100$).
