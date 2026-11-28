# Vanishing of the third cohomology of the multiplicative group of a number field

Let $K$ be a number field with algebraic closure $\bar K$ and absolute Galois group $G_K$. Then

$$H^3(G_K, \bar K^\times) = 0.$$

More generally, for every $r \ge 3$ restriction to the decomposition groups of the real places is an isomorphism
$H^r(G_K, \bar K^\times) \to \bigoplus_{v \text{ real}} H^r(K_v, \mathbb{C}^\times)$, where
$H^r(K_v, \mathbb{C}^\times) = H^r(\operatorname{Gal}(\mathbb{C}/\mathbb{R}), \mathbb{C}^\times)$ is $0$ for odd $r$ and of
order $2$ for even $r$; so $H^r(G_K, \bar K^\times) = 0$ for all odd $r \ge 3$.

Milne's proof, with $S$ the set of all places, so that $G_S = G_K$ and every positive integer lies in
$\mathbb{N}(S)$. As $G_K$ is profinite, $H^3(G_K, \bar K^\times)$ is torsion, and it suffices to show that its
$\ell^n$-torsion vanishes for every prime power $\ell^n$. The Kummer sequence
$0 \to \mu_{\ell^n} \to \bar K^\times \xrightarrow{\ell^n} \bar K^\times \to 0$ and its local analogues give a
commutative diagram with exact rows

$$
\begin{array}{ccccccc}
H^2(G_K, \bar K^\times) & \to & H^3(G_K, \mu_{\ell^n}) & \to & H^3(G_K, \bar K^\times)[\ell^n] & \to & 0 \\
\downarrow & & \downarrow & & \downarrow & & \\
\bigoplus_{v \text{ real}} \mathrm{Br}(K_v) & \to & \bigoplus_{v \text{ real}} H^3(K_v, \mu_{\ell^n}) & \to & \bigoplus_{v \text{ real}} H^3(K_v, \mathbb{C}^\times)[\ell^n] & \to & 0.
\end{array}
$$

The first vertical map is onto, because $\mathrm{Br}(K) \to \bigoplus_v \mathrm{Br}(K_v)$ has cokernel
$\mathbb{Q}/\mathbb{Z}$ through the sum of the invariants and a finite place can absorb any invariant; the second is an
isomorphism since restriction to the real places is an isomorphism on $H^3(G_S, A)$ for finite modules $A$ of order
in $\mathbb{N}(S)$. So the third vertical map is an isomorphism by the five lemma. Finally
$H^3(\operatorname{Gal}(\mathbb{C}/\mathbb{R}), \mathbb{C}^\times) \cong H^1(\operatorname{Gal}(\mathbb{C}/\mathbb{R}), \mathbb{C}^\times) = 0$, by the
periodicity of the cohomology of a cyclic group and Hilbert's Theorem 90. The higher degrees follow by induction
along the same diagram.

## Depends on

- [Cohomology of a profinite group with discrete coefficients](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/cohomology-with-discrete-coefficients.md), for the Galois cohomology of $G_K$

## Proof depends on

- [Finiteness and cohomological dimension of Galois groups with restricted ramification](finiteness-and-cohomological-dimension-of-g-s.md), for the isomorphism $H^i(G_S, A) \to \bigoplus_{v \text{ real}} H^i(K_v, A)$ for $i \ge 3$ (its item 3), applied with $S$ the set of all places and $A = \mu_{\ell^n}$
- [Fundamental class of global class field theory](../../adeles-class-field-theory/reciprocity-law/fundamental-class.md), for the exact sequence $0 \to \mathrm{Br}(K) \to \bigoplus_v \mathrm{Br}(K_v) \to \mathbb{Q}/\mathbb{Z} \to 0$ (its item 1), which makes $\mathrm{Br}(K) \to \bigoplus_{v \text{ real}} \mathrm{Br}(K_v)$ onto
- [Periodicity of Tate cohomology for finite cyclic groups](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/nonempty-periodicity-iso.md), for $H^3 \cong H^1$ over $\operatorname{Gal}(\mathbb{C}/\mathbb{R})$
- [Hilbert's Theorem 90 for the multiplicative group](../../../../FieldTheory/galois-theory/multiplicative-hilbert-s-theorem-90.md), for $H^1(\operatorname{Gal}(\mathbb{C}/\mathbb{R}), \mathbb{C}^\times) = 0$
- [The long exact cohomology sequence](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/long-exact-cohomology-sequence.md), for the long exact sequences
- [Cohomology in positive degrees is torsion](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/cohomology-in-positive-degrees-is-torsion.md), for the torsion of the cohomology of profinite groups in positive degrees

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Corollary 4.18 and its proof (pp. 63–64), applied with $S$ the set of all primes of $K$, and Corollary
  4.21 (p. 66: "$H^r(G_S, \mathbb{G}_m) = 0$ for all odd $r \ge 3$" when $S$ omits only finitely many primes). Milne
  uses the vanishing of $H^3(G_K, K_s^\times)$ in the definitions of the Cassels–Tate pairing, Proposition 6.9 and
  Remark 6.11 (pp. 79–80).
