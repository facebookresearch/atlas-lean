# Green's parametrization of the cuspidal characters of $\mathrm{GL}_n(\mathbb{F}_q)$

Let $q$ be a power of a prime $p$ and $n \ge 1$. An irreducible complex representation of
$\mathrm{GL}_n(\mathbb{F}_q)$ is cuspidal if it does not occur in any representation parabolically
induced from a proper parabolic subgroup, equivalently if it has no nonzero vectors fixed by the
unipotent radical of any proper parabolic subgroup. A character
$\theta \colon \mathbb{F}_{q^n}^\times \to \mathbb{C}^\times$ is regular if the $n$ characters
$\theta, \theta^q, \dots, \theta^{q^{n-1}}$ are distinct, that is, $\theta \neq \theta \circ \sigma$ for
every nontrivial $\sigma \in \mathrm{Gal}(\mathbb{F}_{q^n}/\mathbb{F}_q)$; equivalently $\theta$ does not
factor through the norm map to $\mathbb{F}_{q^d}^\times$ for any proper divisor $d$ of $n$ (A. Prasad's
primitive characters). Then:

1. there is a bijection $\theta \mapsto \pi_\theta$ from the Galois orbits of regular characters of
   $\mathbb{F}_{q^n}^\times$ onto the isomorphism classes of irreducible cuspidal representations of
   $\mathrm{GL}_n(\mathbb{F}_q)$;
2. $\dim \pi_\theta = (q - 1)(q^2 - 1) \cdots (q^{n-1} - 1)$;
3. if $g \in \mathrm{GL}_n(\mathbb{F}_q)$ has irreducible characteristic polynomial, with roots
   $z, z^q, \dots, z^{q^{n-1}}$ in $\mathbb{F}_{q^n}$, then

    $$\operatorname{tr} \pi_\theta(g) = (-1)^{n-1} \sum_{i=0}^{n-1} \theta\bigl(z^{q^i}\bigr).$$

The number of Galois orbits of regular characters equals the number of monic irreducible polynomials of
degree $n$ over $\mathbb{F}_q$ with nonzero constant term, that is, the number of conjugacy classes of
elements of $\mathrm{GL}_n(\mathbb{F}_q)$ with irreducible characteristic polynomial (A. Prasad, after
Theorem 4.1). For $n \ge 2$ every monic irreducible polynomial of degree $n$ has nonzero constant term;
for $n = 1$ the polynomial $T$ is excluded, leaving the $q - 1$ classes of $\mathrm{GL}_1(\mathbb{F}_q)$
and the $q - 1$ characters of $\mathbb{F}_q^\times$, all regular.
For $n = 2$ the cuspidal characters have degree $q - 1$ and value $-(\theta(z) + \theta(z^q))$ on such
elements. The degree is $|\mathrm{GL}_n(\mathbb{F}_q)|_{p'} / |\mathbb{F}_{q^n}^\times|$, the
prime-to-$p$ part of the group order divided by the order of the torus $\mathbb{F}_{q^n}^\times$ (D. Prasad,
Example 5.2(1)).

## Sources

- A. Prasad, *Representations of $GL_2(\mathbb{F}_q)$ and $SL_2(\mathbb{F}_q)$, and some remarks about
  $GL_n(\mathbb{F}_q)$*, lecture notes, Advanced Instructional School, Pune (2007),
  <https://www.imsc.res.in/~amri/notes.pdf>, Chapter 4: Section 4.2 (cuspidal representations, primitive
  characters), Theorem 4.1 (the bijection) and Theorem 4.2 (the character values); the chapter states
  these results of Green without proof. Its count of orbits after Theorem 4.1 omits the condition of a
  nonzero constant term, which matters only for $n = 1$.
- D. Prasad, *Notes on representations of finite groups of Lie type*, arXiv:1404.0861v1 (2014): §4
  (regular characters and Green's classification), Example 5.2 (1) (the dimension
  $\prod_{i=1}^{n-1} (q^i - 1)$) and (3) (the value $-(\chi(x) + \chi(x^\sigma))$ for $n = 2$). His
  Theorem 4.2(ii) prints the sign $(-1)^n$ in the character formula, which disagrees with A. Prasad's
  Theorem 4.2 and with Example 5.2 (1) and (3); the sign $(-1)^{n-1}$ above is the one consistent with
  the degree.
- J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80 (1955),
  402–447, the original source, as cited by both notes.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result for $q = p$ prime, as `GlobalTheory.Published.GreenRegularCharacters`.
