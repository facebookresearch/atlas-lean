# Unramified classes under local duality

Let $k$ be a finite extension of $\mathbb{Q}_p$, $I_k \subseteq G_k$ its inertia group and
$\Gamma = G_k / I_k \cong \operatorname{Gal}(\bar{\mathbb{F}}_q/\mathbb{F}_q) \cong \hat{\mathbb{Z}}$, where
$\mathbb{F}_q$ is the residue field. For a discrete $G_k$-module $A$ let

$$H^1_{\mathrm{nr}}(k, A) = \operatorname{im}\bigl(H^1(\Gamma, A^{I_k}) \xrightarrow{\ \inf\ } H^1(k, A)\bigr),$$

the group of unramified classes. Inflation is injective here, and $H^1_{\mathrm{nr}}(k, A)$ is the kernel of
the restriction map $H^1(k, A) \to H^1(I_k, A)$. For finite $A$,
$\# H^1_{\mathrm{nr}}(k, A) = \# H^0(k, A)$: the sequence
$0 \to H^0(k, A) \to A^{I_k} \xrightarrow{\mathrm{Frob} - 1} A^{I_k} \to H^1(\Gamma, A^{I_k}) \to 0$ is exact.

Let $A$ be a finite $G_k$-module of order prime to $p$, and $A' = \operatorname{Hom}(A, \mu)$. Then under
the perfect pairing $H^1(k, A) \times H^1(k, A') \to \mathbb{Q}/\mathbb{Z}$ of local Tate duality, the
subgroups $H^1_{\mathrm{nr}}(k, A)$ and $H^1_{\mathrm{nr}}(k, A')$ are the exact annihilators of each other.
When $A$ is unramified ($I_k$ acts trivially), so is $A'$, and $H^1_{\mathrm{nr}}(k, A) = H^1(\Gamma, A)$.

More generally, put $H^i_{\mathrm{nr}}(k, A) = \operatorname{im}(H^i(\Gamma, A^{I_k}) \to H^i(k, A))$ for all $i$. If
$A$ is finite, unramified and of order prime to $p$, then $H^0_{\mathrm{nr}}(k, A) = H^0(k, A)$,
$H^2_{\mathrm{nr}}(k, A) = H^2_{\mathrm{nr}}(k, A') = 0$ since $\operatorname{cd} \Gamma = 1$, and for $0 \le i \le 2$ the
groups $H^i_{\mathrm{nr}}(k, A')$ and $H^{2-i}_{\mathrm{nr}}(k, A)$ are exact annihilators of each other under the
pairing $H^i(k, A') \times H^{2-i}(k, A) \to \mathbb{Q}/\mathbb{Z}$.

## Depends on

- [Local Tate duality](local-tate-duality.md), for the pairing
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for inflation and restriction

## Proof depends on

- [Local Tate duality](local-tate-duality.md)
- [Local Euler characteristic formula](local-euler-characteristic-formula.md), for $\# H^1(k, A) = \# H^0(k, A) \cdot \# H^2(k, A)$ when the order of $A$ is prime to $p$, which with duality gives $\# H^1_{\mathrm{nr}}(k, A) \cdot \# H^1_{\mathrm{nr}}(k, A') = \# H^1(k, A)$
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for the cohomology of $\hat{\mathbb{Z}}$ (cohomological dimension $1$, and $\# H^0 = \# H^1$ on finite modules), which makes the cup product of two unramified classes vanish, and for the inflation–restriction sequence
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the cohomological triviality of the units of the maximal unramified extension (its item 1), which gives the orthogonality in degrees $0$ and $2$ for unramified $A$ (NSW, proof of (7.2.15), through (7.1.2)(i))

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: (7.2.14) Definition (the
  unramified cohomology groups $H^i_{\mathrm{nr}}$), (7.2.15) Theorem ($H^i_{\mathrm{nr}}(k, A^d)$ and
  $H^{2-i}_{\mathrm{nr}}(k, A)$ are mutually orthogonal complements for $A$ finite and unramified, of order prime
  to the residue characteristic, where then $A^d = A'$), pp. 387–389, and Chapter VII, §2, Exercise 2 (the
  same for finite $A$ of order prime to the residue characteristic, not necessarily unramified).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Theorem 2.6 and the remark at the end of its proof (the counting argument of Serre's
  *Cohomologie galoisienne*, II 5.5, for finite $M$).
- H. Darmon, F. Diamond, R. Taylor, "Fermat's Last Theorem", 1995,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: Theorem 2.17 (e) and the exact
  sequence at the top of p. 61 ($\# H^1(G_v/I_v, M^{I_v}) = \# H^0(G_v, M)$).
- J. Bellaïche, *An introduction to the conjecture of Bloch and Kato*, Clay Mathematics Institute summer
  school, 2009, <http://virtualmath1.stanford.edu/~conrad/BSDseminar/refs/BKintro.pdf>: Proposition 2.3 and its
  proof (the counting argument, for $p$-adic coefficients).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the unramified case as `ReciprocityTheory.Gal.UnramifiedOrthogonality`, and the unramified classes
  as `Formalism.GaloisCohomology.unrK`.
