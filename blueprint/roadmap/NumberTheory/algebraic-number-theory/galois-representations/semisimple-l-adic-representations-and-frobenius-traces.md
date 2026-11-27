# Semisimple ℓ-adic representations are determined by their Frobenius traces

Let $\ell$ be a prime, $K$ a finite extension of $\mathbb{Q}_\ell$ and $S$ a finite set of primes. Let
$\rho, \rho' \colon G_{\mathbb{Q}} \to \mathrm{GL}_d(K)$ be semisimple
[ℓ-adic representations](conductor-of-an-l-adic-representation.md), that is, continuous representations, unramified
at all but finitely many primes, that are direct sums of irreducible ones. If
$\operatorname{tr} \rho(\mathrm{Frob}_p) = \operatorname{tr} \rho'(\mathrm{Frob}_p)$ for every prime $p \notin S$ at which
$\rho$ and $\rho'$ are unramified, then $\rho \cong \rho'$. Here $\mathrm{Frob}_p$ is an arithmetic Frobenius element at
a prime of $\overline{\mathbb{Q}}$ above $p$, and the trace does not depend on its choice when the representation is
unramified at $p$.

Darmon, Diamond and Taylor state this as: a semisimple $\ell$-adic representation is determined by the values of
$\operatorname{tr} \rho(\mathrm{Frob}_p)$ on the primes $p \notin S$ at which $\rho$ is unramified.

## Expansion

This node is still to be broken down. A good expansion states and links:

1. the equality $\operatorname{tr} \rho = \operatorname{tr} \rho'$ on all of $G_{\mathbb{Q}}$: by the
   [Chebotarev density theorem](../adeles-class-field-theory/chebotarev-density-theorem.md), applied to the finite
   Galois extensions of $\mathbb{Q}$ unramified outside $S$ and the primes where $\rho$ or $\rho'$ ramifies, the Frobenius
   elements at the remaining primes are dense, and $\operatorname{tr} \rho$ and $\operatorname{tr} \rho'$ are continuous and
   constant on conjugacy classes;
2. the determination, up to isomorphism, of a semisimple finite-dimensional representation of a group over a field of
   characteristic $0$ by its character (Bourbaki, *Algèbre*, Chapter VIII, §12.1, Proposition 3, as cited by
   Darmon–Diamond–Taylor, p. 54; not read here).

## Depends on

- [Conductor of an ℓ-adic representation](conductor-of-an-l-adic-representation.md), for $\ell$-adic representations of $G_{\mathbb{Q}}$ and unramified primes
- [Galois representations attached to normalized eigenforms](../../not-yet-classified/exists-galois-rep-charpoly-frob.md), for arithmetic Frobenius elements at the primes of $\overline{\mathbb{Z}}$

## Proof depends on

- [Chebotarev density theorem](../adeles-class-field-theory/chebotarev-density-theorem.md), for the density of Frobenius elements (expansion item 1)

## Sources

- H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", *Current Developments in Mathematics* 1 (1995),
  International Press; page numbers of the authors' text at
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: p. 53 (ℓ-adic representations,
  "We require that an ℓ-adic representation be unramified at all but finitely many primes", and Remark 2.5 (c), on
  representations that are not semisimple) and Proposition 2.6, pp. 53–54, part (c), p. 54: "A semi-simple ℓ-adic
  representation $\rho \colon G_{\mathbb{Q}} \to \mathrm{GL}_d(K)$ is determined by the values of $\operatorname{tr} \rho(\mathrm{Frob}\, p)$
  on the primes $p \notin S$ at which $\rho$ is unramified", with its proof: "Combining the Chebotarev density theorem
  (theorem 2.3) with the continuity of $\rho$ we see that we must show that $\operatorname{tr} \rho$ (resp.
  $\operatorname{tr} \wedge^i \rho$) determines $\rho$ up to conjugacy in the various settings. For the characteristic zero
  representations, see [Bour], ch. 8, sec. 12.1, prop. 3".
