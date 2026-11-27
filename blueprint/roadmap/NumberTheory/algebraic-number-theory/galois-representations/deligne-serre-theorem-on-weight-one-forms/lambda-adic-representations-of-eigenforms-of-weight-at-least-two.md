# λ-adic representations attached to eigenforms of weight at least two

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ and $k \ge 2$ an integer with
$\varepsilon(-1) = (-1)^k$, and let $f \ne 0$ be a modular form of type $(k, \varepsilon)$ on $\Gamma_0(N)$ (as on
[Rankin's bound](rankin-bound-for-the-mean-square-of-hecke-eigenvalues.md); $f$ need not be a cusp form) that is an
eigenvector of the Hecke operators $T_p$, $p \nmid N$, with eigenvalues $a_p$. Let $K$ be a finite extension of
$\mathbb{Q}$ containing the $a_p$ and the $\varepsilon(p)$, let $\lambda$ be a finite place of $K$ with residue
characteristic $\ell$, and let $K_\lambda$ be the completion of $K$ at $\lambda$. Then there is a continuous semisimple
representation

$$\rho_\lambda \colon G \to \mathrm{GL}_2(K_\lambda), \qquad G = \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}),$$

unramified outside $N\ell$, such that

$$\operatorname{Tr}(F_{\rho_\lambda,p}) = a_p \qquad \text{and} \qquad \det(F_{\rho_\lambda,p}) = \varepsilon(p)\, p^{k-1} \qquad \text{for every prime } p \nmid N\ell,$$

where unramified, $F_{\rho_\lambda,p}$ (the image of the arithmetic Frobenius) and continuity are as on
[Semisimple Galois representations with the same Frobenius polynomials](semisimple-galois-representations-with-equal-frobenius-polynomials.md),
$K_\lambda$ carrying its $\lambda$-adic topology. By that lemma these conditions determine $\rho_\lambda$ up to isomorphism.

This is Théorème 6.1 of Deligne–Serre, which they use without proof: in the introduction they ask the reader to accept
it until a complete proof by Deligne is published. Their Remarque 6.2 says how it is obtained: for an Eisenstein series
from Hecke's results, taking for $\rho_\lambda$ the direct sum of two representations of degree $1$; for a cusp form it
is proved in a special case by Deligne [4], and the general case is treated by another method by Langlands [11].

## Depends on

- [Semisimple Galois representations with the same Frobenius polynomials are isomorphic](semisimple-galois-representations-with-equal-frobenius-polynomials.md), for the conventions on unramified representations and Frobenius elements

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the representations of the normalized eigenforms of weight $k = 2$ and of weight $k \ge 3$, which are the cases
  $k \ge 2$ of [Diamond–Shurman's Theorem 9.6.5](../../../not-yet-classified/exists-galois-rep-charpoly-frob.md) (its case
  $k = 1$ is Théorème 4.1 itself);
- the reduction of a cuspidal $f$ to a primitive form: by the decomposition of §1.9 a cusp form that is an eigenvector
  of the $T_p$, $p \nmid N$, has the eigenvalues $a_p$, $p \nmid N$, of a primitive form of level dividing $N$, whose
  representations are defined over the completions of its own field of coefficients;
- the realization of the representation over the given completion $K_\lambda$, which contains its traces and
  determinants;
- the Eisenstein case: the eigenvalues of an Eisenstein series that is an eigenvector of the $T_p$, from Hecke's
  results ([9], p. 690, as cited in Deligne–Serre (1974), p. 521), and the two characters of degree $1$, a Dirichlet
  character and one twisted by a power of the $\ell$-adic
  [cyclotomic character](../cyclotomic-character-and-tate-twists.md), whose sum is $\rho_\lambda$.

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): Théorème 6.1 and (6.1.1), p. 520 ("Soit f une forme
  modulaire de type (k, ε) sur Γ₀(N), non identiquement nulle. On suppose que k ≧ 2 et que f est fonction propre des
  $T_p$, $p \nmid N$, avec pour valeurs propres $a_p$"); Remarque 6.2, p. 521; the introduction, p. 507, on the use of
  results of Deligne without published proof; §3.1 and footnote (1), pp. 512–513.
- P. Deligne, *Formes modulaires et représentations l-adiques*, Séminaire Bourbaki, exp. 355 (1968/69), Lecture Notes in
  Math. 179, Springer (1971), 139–172; R. P. Langlands, *Modular forms and l-adic representations*, Lecture Notes in
  Math. 349, Springer (1973), 361–500; E. Hecke, *Mathematische Werke*, p. 690: each as cited in Deligne–Serre (1974),
  p. 521; not read.
