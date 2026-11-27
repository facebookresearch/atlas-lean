# Irreducibility of the Galois representations of weight-two eigenforms

This node is still to be broken down. Let $N \ge 1$, let $f \in S_2(\Gamma_1(N))$ be a normalized eigenform with
nebentypus $\chi$, number field $K_f = \mathbb{Q}(a_n(f) : n \ge 1)$, $\ell$ a prime and $\lambda$ a maximal ideal of
$\mathcal{O}_{K_f}$ over $\ell$, as in
[Galois representations attached to weight-two eigenforms](galois-representations-attached-to-weight-two-eigenforms.md).
Let $\rho \colon G_{\mathbb{Q}} \to \mathrm{GL}_2(K_{f,\lambda})$ be any continuous representation with the two properties
of that page: unramified at every prime $p \nmid \ell N$, and with characteristic polynomial
$X^2 - a_p(f) X + \chi(p) p$ at every arithmetic Frobenius element at a maximal ideal of $\overline{\mathbb{Z}}$ over such a $p$.
Then $\rho$ is irreducible: no line of $K_{f,\lambda}^2$ is stable under every $\rho(\sigma)$, $\sigma \in G_{\mathbb{Q}}$.

The sources state this for the representation $\rho_{f,\lambda}$ that Shimura's construction attaches to $f$. A
representation $\rho$ as above has the same Frobenius characteristic polynomials outside $\ell N$; if it stabilized a
line, its semisimplification would be a sum of two characters with those characteristic polynomials, and by the
Chebotarev density theorem it would be isomorphic to the semisimplification of $\rho_{f,\lambda}$, which is irreducible.

## Depends on

- [Galois representations attached to weight-two eigenforms](galois-representations-attached-to-weight-two-eigenforms.md), for $f$, $K_{f,\lambda}$ and the two properties of $\rho$

## Proof depends on

- [Galois representations attached to weight-two eigenforms](galois-representations-attached-to-weight-two-eigenforms.md), for the representation $\rho_{f,\lambda}$ of Shimura's construction
- [Chebotarev density theorem](../../adeles-class-field-theory/chebotarev-density-theorem.md), for the comparison of $\rho$ with $\rho_{f,\lambda}$ through their Frobenius characteristic polynomials

## Expansion

This node is still to be broken down. A good expansion states and links:

- Ribet's theorem that $\rho_{f,\lambda}$ is irreducible (Ribet, Theorem 2.3, as cited by Diamond–Im): assuming
  reducibility, the algebraicity results of Lang and Serre on abelian $\ell$-adic representations contradict the
  estimate $|a_n| \le c(f)\,\sigma_0(n)\sqrt{n}$ on the Fourier coefficients (Darmon–Diamond–Taylor, proof of
  Theorem 3.1 (c), p. 86, and their Theorem 1.24, p. 33);
- the determination of a semisimple continuous $\ell$-adic representation by the characteristic polynomials of
  Frobenius elements outside a finite set of primes (Darmon–Diamond–Taylor, Proposition 2.6 (c), from the Chebotarev
  density theorem), and the comparison of a reducible $\rho$ with $\rho_{f,\lambda}$ through semisimplifications.

## Sources

- F. Diamond and J. Im, "Modular forms and modular curves", Canadian Mathematical Society Conference
  Proceedings 17 (1995), cited by section and remark numbers: §12.5, Remark 12.5.4 ("The representations $\rho_\lambda$
  are known to be irreducible [Rib1, Theorem 2.3]").
- H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", page numbers of the authors' text at
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: §3.1, Theorem 3.1 (c), pp. 85–86
  ("$\rho$ is absolutely irreducible", for a newform of weight two), and p. 86 ("Part (c) was proved by Ribet (see
  section 2 of [R3]). Assuming reducibility of the representation, he applies algebraicity results of Lang and Serre to
  obtain a contradiction to the estimate on the Fourier coefficients stated in theorem 1.24"); Proposition 2.6 (c),
  pp. 53–54.
- K. A. Ribet, Theorem 2.3 and §2 of his paper on the $\ell$-adic representations attached to eigenforms with
  Nebentypus, pp. 17–52 of a volume of *Modular Functions of One Variable* (Lecture Notes in Math., Springer, 1977),
  as cited by Diamond–Im (Remark 12.5.4; their bibliography gives "Galois representations attached to eigenforms
  with Nebentypus" in volume VI, Lecture Notes in Math. 627) and by Darmon–Diamond–Taylor (proof of Theorem 3.1;
  their bibliography gives "The $\ell$-adic representations attached to an eigenform with Nebentypus: a survey" in
  volume V, Lecture Notes in Math. 601); not read for this page.
