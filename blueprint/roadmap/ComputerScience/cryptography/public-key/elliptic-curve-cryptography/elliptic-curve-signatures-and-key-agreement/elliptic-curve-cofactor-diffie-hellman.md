# Elliptic-curve cofactor Diffie–Hellman

The elliptic-curve Diffie–Hellman primitive outputs the $x$-coordinate of $[d_U]Q_V$; the cofactor variant outputs that of $[h\,d_U]Q_V$, a point of order dividing $n$ for every curve point $Q_V$, and both reject the point at infinity.

Let $T=(p,a,b,G,n,h)$ be valid SEC 1 elliptic-curve domain parameters ($G$ of prime order $n$ and $h=\#E(\mathbb{F}_p)/n$; validity implies $n\nmid h$, as shown on the public-key validation page), let $d_U\in[1,n-1]$ be the private key of $U$, and let $Q_V$ be a public key purportedly of $V$.

- **ECDH primitive** (for a fully valid $Q_V$): compute $P=[d_U]Q_V$; if $P=O$ output "invalid"; otherwise output the shared secret $z=x_P$.
- **Cofactor ECDH primitive** (for a partially valid $Q_V$): compute $P=[h\,d_U]Q_V$; if $P=O$ output "invalid"; otherwise output $z=x_P$.

If $Q_U=[d_U]G$ and $Q_V=[d_V]G$ with $d_U,d_V\in[1,n-1]$, both parties compute the same point, $[d_U]Q_V=[d_V]Q_U=[d_Ud_V]G$ and $[hd_U]Q_V=[hd_V]Q_U=[hd_Ud_V]G$, and these points are not $O$ because $n$ is prime and $n\nmid hd_Ud_V$; so both parties obtain the same $z$. For every $Q\in E(\mathbb{F}_p)$ the point $[h]Q$ satisfies $[n]\,([h]Q)=[\#E(\mathbb{F}_p)]Q=O$, so it lies in $\langle G\rangle$; in the cofactor primitive the cleared point $[h]Q_V$ and the result $P$ therefore lie in $\langle G\rangle$ even when $Q_V$ is merely partially valid, which SEC 1 uses to resist small-subgroup attacks. Points arising inside the computation of a scalar multiple of $Q_V$ need not lie in $\langle G\rangle$, and nothing is claimed about side channels.

## Depends on

- [Correctness of Diffie–Hellman key agreement](../../diffie-hellman-key-exchange/dh-agree.md)
- [Elliptic-curve public key validation](elliptic-curve-public-key-validation.md)

## Proof depends on

- [Lagrange's theorem](../../../../../GroupTheory/group-basics/lagrange-theorem.md)

## Expansion

Agreement is the commutativity $[a]\,([b]G)=[b]\,([a]G)$ of scalar multiplication, the additive form of Diffie–Hellman correctness. The claim about $[h]Q$ is Lagrange's theorem in $E(\mathbb{F}_p)$ of order $hn$, and $E(\mathbb{F}_p)[n]=\langle G\rangle$ because $n\nmid h$. For honest keys the two primitives output the $x$-coordinates of $[d_Ud_V]G$ and $[hd_Ud_V]G$; they coincide when $h=1$, and in general they may or may not give the same field element. These primitives give agreement on a shared secret; they provide no authentication.

## Sources

- Certicom Research, *SEC 1: Elliptic Curve Cryptography*, Standards for Efficient Cryptography, version 2.0, 2009, <https://www.secg.org/sec1-v2.pdf>, Sections 3.1.1, 3.3, 3.3.1 and 3.3.2.
- S. D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press, 2012, doi:10.1017/CBO9781139012843; numbering from the author's extended and corrected version 2.0 chapters, <https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html>, Section 11.6 (forcing elements into the subgroup by multiplying by the cofactor).
