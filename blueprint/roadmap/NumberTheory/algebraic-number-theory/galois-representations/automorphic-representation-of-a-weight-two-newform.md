# Automorphic representation of a newform of weight two

Let $N \ge 1$ and let $f = \sum_{n \ge 1} a_n q^n$ be a newform of weight $2$ and level $N$ in the sense of
Darmon, Diamond and Taylor: an element of $S_2(\Gamma_1(N))$ with $a_1 = 1$ that is an eigenvector of the Hecke
operators $T_p$ ($p \nmid N$) and $U_q$ ($q \mid N$), which are the
[Hecke operators](../../modular-forms-q-series/modular-forms/hecke-operators-of-level-n.md) $T_p$ and $T_q$ on $S_2(\Gamma_1(N))$, and of the
diamond operators $\langle d \rangle f(\tau) = (c\tau + d)^{-2} f\bigl(\tfrac{a\tau + b}{c\tau + d}\bigr)$ for
$\left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right) \in \Gamma_0(N)$, and that lies in the new subspace,
the orthogonal complement, for the Petersson scalar product
$\langle f, g \rangle = \int_{\mathcal{H}/\Gamma_1(N)} f(\tau)\overline{g(\tau)}\,dx\,dy$ ($\tau = x + iy$), of the span of the
forms $g(a\tau)$ with $g \in S_2(\Gamma_1(M))$, $M < N$ and $aM \mid N$. Let $\psi \colon (\mathbb{Z}/N\mathbb{Z})^\times \to \mathbb{C}^\times$
send $d$ to the eigenvalue of $\langle d \rangle$ on $f$, so that $f$ has nebentypus $\psi$ in the convention of
[Galois representations attached to normalized eigenforms](../../not-yet-classified/exists-galois-rep-charpoly-frob.md):
$f\bigl(\tfrac{a\tau + b}{c\tau + d}\bigr) = \psi(d)(c\tau + d)^2 f(\tau)$ for
$\left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right) \in \Gamma_0(N)$.

Let $\omega$ be the adelization of $\psi$: the character of $\mathbb{A}_{\mathbb{Q}}^\times$, trivial on $\mathbb{Q}^\times$, with
$\omega(\varpi_p) = \psi(p)$ for every prime $p \nmid N$, where $\varpi_p \in \mathbb{Q}_p^\times \subset \mathbb{A}_{\mathbb{Q}}^\times$ is a
uniformizer at $p$; let $\omega_p$ be its restriction to $\mathbb{Q}_p^\times$. Let
$K_0(N) \subset \mathrm{GL}_2(\widehat{\mathbb{Z}})$ be the subgroup of the matrices
$\left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right)$ with $c \equiv 0 \pmod N$, and $\lambda$ its character
$\left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right) \mapsto \prod_{p \mid N} \omega_p(d_p)$. The adelic form of $f$ is
the function $\varphi_f$ on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ with

$$\varphi_f(\gamma g_\infty k) = f(g_\infty(i))\,(ci + d)^{-2}\,\det(g_\infty)\,\lambda(k)$$

for $\gamma \in \mathrm{GL}_2(\mathbb{Q})$, $g_\infty = \left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right) \in \mathrm{GL}_2(\mathbb{R})$
with $\det(g_\infty) > 0$, and $k \in K_0(N)$. Then:

1. For the maximal compact subgroup $K = K_\infty\,\mathrm{GL}_2(\widehat{\mathbb{Z}})$ of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, $K_\infty = \mathrm{O}(2)$, the
   function $\varphi_f$ is an automorphic form with central character $\omega$; the
   $\mathcal{H}$-submodule $\pi = \varphi_f \ast \mathcal{H}$ of the space $\mathcal{A}(\mathrm{GL}_2)$ of automorphic forms that it generates under
   right convolution by the global Hecke algebra $\mathcal{H}$, spanned by the functions $D\,R(k_\infty g_f)\varphi_f$ with
   $D \in \mathcal{U}(\mathfrak{g})$, $k_\infty \in K_\infty$ and $g_f \in \mathrm{GL}_2(\mathbb{A}_f)$, where $R$ is right translation and $\mathfrak{g}$
   the complexified Lie algebra of $\mathrm{GL}_2(\mathbb{R})$, is irreducible, an automorphic representation; so, by the
   tensor product theorem, $\pi \cong \bigotimes'_v \pi_v$, with $\pi_p$ an irreducible admissible representation of
   $\mathrm{GL}_2(\mathbb{Q}_p)$ for every prime $p$ and $\pi_\infty$ an irreducible admissible $(\mathfrak{g}, K_\infty)$-module;
2. for every prime $p$, $\varphi_f$ is a new vector of $\pi_p$: the conductor of $\pi_p$ in the sense of
   [Casselman's theorem on local newforms](local-newforms-for-gl-2.md) is $\mathfrak{c}(\pi_p) = p^{v_p(N)}\mathbb{Z}_p$;
3. for every prime $p \nmid N$, $\pi_p \cong \mathrm{Ind}(\xi_1, \xi_2)$ for unramified characters $\xi_1, \xi_2$ of
   $\mathbb{Q}_p^\times$ such that $\xi_1(p)p^{1/2}$ and $\xi_2(p)p^{1/2}$ are the roots of $X^2 - a_p X + \psi(p)\,p$, where
   $\mathrm{Ind}(\xi_1, \xi_2)$ is the [normalized parabolic induction](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md)
   from the upper triangular Borel subgroup of the character
   $\left(\begin{smallmatrix} a & 0 \\ 0 & b \end{smallmatrix}\right) \mapsto \xi_1(a)\xi_2(b)$ of the diagonal torus: the
   smooth functions $\phi$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ with
   $\phi\bigl(\left(\begin{smallmatrix} a & x \\ 0 & b \end{smallmatrix}\right) g\bigr) = \xi_1(a)\xi_2(b)\lvert a/b \rvert^{1/2} \phi(g)$,
   under right translation.

This is Loeffler and Weinstein's construction for weight $k = 2$ and character $\varepsilon = \psi$. They write $\pi$ as the
span of the right translates of $\varphi_f$ under all of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$; but right translation by $\mathrm{GL}_2(\mathbb{R})$
does not preserve $K_\infty$-finiteness, so the space of automorphic forms is a module over $\mathcal{H}$ rather than a
representation of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, and the representation of clause 1 is the $\mathcal{H}$-module that $\varphi_f$
generates, which is admissible (Cogdell, Lecture 2, §3, Lecture 3, §1, and Theorem 3.1). Their new vectors
are those of Casselman's theorem with $\omega(d)$ in place of Casselman's $\omega(a)$, which they note is equivalent, so
that their conductor of $\pi_p$ is the exponent of $\mathfrak{c}(\pi_p)$. Their principal series $\pi(\xi_1, \xi_2)$, defined when
$\xi_1/\xi_2 \neq \lvert\cdot\rvert^{\pm 1}$ and with central character $\xi_1\xi_2$, is Casselman's principal series: his
$\varrho(\xi_1, \xi_2)$ on the space $\mathcal{B}(\xi_1, \xi_2)$, which is irreducible unless $\xi_1\xi_2^{-1} = \lvert\cdot\rvert^{\pm 1}$, the
induced representation of clause 3.

## Expansion

This node is still to be broken down. A good expansion states and links:

1. the adelic form: $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) = \mathrm{GL}_2(\mathbb{Q})\,\mathrm{GL}_2(\mathbb{R})^+ K_0(N)$ (Loeffler–Weinstein, citing
   Bump, Theorem 3.3.1; not read here) and $\mathrm{GL}_2(\mathbb{Q}) \cap \mathrm{GL}_2(\mathbb{R})^+ K_0(N) = \Gamma_0(N)$, so that
   $\varphi_f$ is well defined, $\varphi_f(gz) = \omega(z)\varphi_f(g)$ for $z$ in the centre, and $\varphi_f$ lies in Loeffler and
   Weinstein's space $\mathcal{A}_0(\omega)$ of automorphic forms with central character $\omega$ (citing Gelbart, §3; not read
   here);
2. the irreducibility of $\pi$ and its decomposition: the decomposition of the space of cusp forms into irreducible
   representations occurring with multiplicity one, and strong multiplicity one, as in Casselman's Theorem 2 (p. 307)
   and his account on p. 312, which put the forms with the same Hecke eigenvalues at almost all primes in one
   irreducible representation, with the tensor product decomposition of its local components;
3. the new vectors: for $p \mid N$, $\pi_p(k)\varphi_f = \omega_p(d)\varphi_f$ for $k = \left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right)$
   in the component at $p$ of $K_0(N)$, whose entry $d$ is a unit, and for $p \nmid N$, $\varphi_f$ is fixed by
   $\mathrm{GL}_2(\mathbb{Z}_p)$; Casselman's Theorem 1 and Corollary (pp. 302 and 306) for the dimensions of the spaces of
   vectors of each level, and his Theorem 4 (p. 313) with the sentence after it, "All newforms arise in
   this way", so that the level $N$ of a newform is the conductor; with the agreement of the newforms above with those
   of Atkin and Lehner, through the decomposition of $S_2(\Gamma_1(N))$ along the newforms of levels dividing $N$
   (Darmon–Diamond–Taylor, Theorem 1.22, citing Atkin–Lehner and Lang, Chapter VIII; not read here);
4. the unramified components: the eigenvalue $\lambda(\pi_p) = a_p p^{-1/2}$ of Loeffler and Weinstein's normalized
   operator $T_p$ on the new vector, and the eigenvalue $\xi_1(p) + \xi_2(p)$ on the vector of $\pi(\xi_1, \xi_2)$ fixed by
   $\mathrm{GL}_2(\mathbb{Z}_p)$ (their Table 1), which with the central character, $\xi_1(p)\xi_2(p) = \omega_p(p) = \psi(p)$, give
   the roots $\xi_1(p)p^{1/2}$ and $\xi_2(p)p^{1/2}$ of $X^2 - a_p X + \psi(p)\,p$.

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for automorphic forms on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, the global Hecke algebra $\mathcal{H}$ acting on them by right convolution, and automorphic representations
- [Tensor product theorem for automorphic representations](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/tensor-product-theorem.md), for the local components $\pi_v$, irreducible admissible representations of $\mathrm{GL}_2(\mathbb{Q}_p)$ at the primes and a $(\mathfrak{g}, K_\infty)$-module at the real place
- [Hecke operators $T_n$ on weight-two cusp forms for a group of level $N$](../../modular-forms-q-series/modular-forms/hecke-operators-of-level-n.md), for the operators $T_p$ ($p \nmid N$) and $U_q = T_q$ ($q \mid N$) on $S_2(\Gamma_1(N))$
- [Galois representations attached to normalized eigenforms](../../not-yet-classified/exists-galois-rep-charpoly-frob.md), for the nebentypus convention $f \mid_2 \gamma = \psi(d) f$, $\gamma \in \Gamma_0(N)$
- [Casselman's theorem on local newforms for GL₂](local-newforms-for-gl-2.md), for the new vectors and the conductor $\mathfrak{c}(\pi_p)$
- [Parabolic induction and Jacquet functors](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md), for the normalized induction $\mathrm{Ind}(\xi_1, \xi_2)$ from the upper triangular Borel subgroup of $\mathrm{GL}_2(\mathbb{Q}_p)$

## Proof depends on

- [Casselman's theorem on local newforms for GL₂](local-newforms-for-gl-2.md), for the dimensions of the spaces of vectors of level $\mathfrak{c}(\pi_p)p^i$ behind Casselman's Theorem 4 (expansion item 3)
- [Multiplicity one for GLₙ](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n/multiplicity-one-for-gl-n.md), for the decomposition of the space of cusp forms into irreducible representations occurring once each (expansion item 2)
- [Strong multiplicity one for GLₙ](../../../RepresentationTheory/automorphic-representations/automorphic-representations-of-gl-n/strong-multiplicity-one-for-gl-n.md), for Casselman's Theorem 2, which puts the forms with the same components at almost all places in one irreducible representation (expansion item 2)

## Sources

- D. Loeffler and J. Weinstein, "On the computation of local components of a newform", Math. Comp. 81 (2012),
  no. 278, 1179–1200, doi:10.1090/S0025-5718-2011-02530-5:
  - §1.1, p. 1179: for a newform $f$ for $\Gamma_1(N)$ of weight $k \ge 2$ and character $\varepsilon$, "the component $\pi_{f,p}$ for a
    prime $p \nmid N$ is the unramified principal series with Satake parameters equal to the roots of the polynomial
    $X^2 - a_pX + \varepsilon(p)p^{k-1}$";
  - §2.1, pp. 1180–1181: "Let $\omega$ be the adelization of $\varepsilon$; that is, $\omega$ is the unique character of $Z_{\mathbb{A}}/Z_{\mathbb{Q}}$
    such that $\omega(\varpi_p) = \varepsilon(p)$ for primes $p \nmid N$"; $K_0(N)$, the character $\lambda$ and the function
    $\varphi_f(\gamma g_\infty k_0) = f(g_\infty(i)) \cdot (ci + d)^{-k} \cdot (\det g_\infty)^{k/2} \cdot \lambda(k_0)$; "The function $\varphi_f$ in fact
    lies in the space $\mathcal{A}_0(\omega)$ of automorphic forms on $G_{\mathbb{A}}$ of central character $\omega$ … We define $\pi_f$ to
    be the linear span of the right translates of $f$ under $G_{\mathbb{A}}$ … If $f$ is an eigenform, then it is well known
    that this representation is irreducible and decomposes as a restricted tensor
    product $\bigotimes'_v \pi_{f,v}$ of admissible irreducible representations of $\mathrm{GL}_2(\mathbb{Q}_v)$";
  - §2.2, pp. 1181–1182: Theorem 2.2 (Casselman's theorem, with $\pi\left(\begin{smallmatrix} a & b \\ c & d \end{smallmatrix}\right)v = \omega(d)v$),
    Remark 2.3 ("Casselman uses $\omega(a)$ rather than $\omega(d)$, but his theorem and Theorem 2.2 are clearly
    equivalent"), Definition 2.4 (the conductor $r(\pi)$ and new vectors), the operator $T_p$ and $\lambda(\pi)$, Table 1 (the
    principal series $\pi(\chi_1, \chi_2)$, defined when $\chi_1/\chi_2 \neq \lvert\cdot\rvert^{\pm 1}$, with central character $\chi_1\chi_2$
    and $\lambda(\pi) = \chi_1^\ast(p) + \chi_2^\ast(p)$), and "If $f$ is a $p$-new eigenform, the automorphic form $\varphi_f$ constructed
    above is a new vector for $\pi_{f,p}$ for every prime $p$. One checks that $\lambda(\pi_{f,p}) = a_p(f)/p^{(k-1)/2}$. In
    particular, if $p \nmid N$, then $\pi_{f,p} \cong \pi(\chi_1, \chi_2)$ with $\chi_1$ and $\chi_2$ the unramified characters whose
    values at $p$ are $\{\alpha/p^{(k-1)/2}, \beta/p^{(k-1)/2}\}$, for $\alpha$ and $\beta$ the roots of $X^2 - a_pX + \omega(p)p^{k-1}$"
    (p. 1182).
- J. W. Cogdell, "Lectures on L-functions, converse theorems, and functoriality for GL_n", in J. W. Cogdell,
  H. H. Kim and M. R. Murty, *Lectures on Automorphic L-functions*, Fields Institute Monographs 20, American
  Mathematical Society, 2004; page numbers of the author's version at
  <https://people.math.osu.edu/cogdell.1/fields-www.pdf>:
  - Lecture 2, §3, p. 17: "One would hope to be able to analyze $A$ as a representation of $\mathrm{GL}_n(\mathbb{A})$ acting by
    right translation. Unfortunately, this is not possible since condition (ii) in the definition of automorphic
    forms is not preserved under right translation. More specifically, it is being $K_\infty$-finite that is not
    preserved under right translation by $G_\infty$.";
  - Lecture 3, §1, p. 21: "the space $A$ of ($K$-finite) automorphic forms does not give a representation of $G(\mathbb{A})$.
    It will be a representation space for the global Hecke algebra $H$"; §1.0.1, pp. 21–22 (the restricted tensor
    product $H = \otimes' H_v$, with $H_v = U(\mathfrak{g}_v) \otimes_{U(\mathfrak{k}_v)} A(K_v)$ at an archimedean place); §1.0.2, p. 22
    ("The space $A$ of $K$-finite automorphic forms is naturally an $H$-module by right convolution");
  - Theorem 3.1, p. 23: "Suppose $\phi \in A$. Then the $H$-module generated by $\phi$, namely
    $V_\phi = R(H)\phi = \phi \ast H \subset A$, is an admissible $H$-module", and Definition 3.2, p. 23 (automorphic
    representations as irreducible subquotients of $A$).
- W. Casselman, "On some results of Atkin and Lehner", Math. Ann. 201 (1973), 301–314:
  - §1: Theorem 1, p. 302, and the Corollary to the Proof, p. 306; p. 304, the space $\mathcal{B}(\mu_1, \mu_2)$ of
    locally constant functions $f$ on $\mathrm{GL}_2(k)$ with $f\bigl(\left(\begin{smallmatrix} a & x \\ 0 & b \end{smallmatrix}\right) g\bigr) =
    \mu_1(a) \cdot \mu_2(b) \cdot \lvert a/b \rvert^{1/2} \cdot f(g)$ and its right regular representation $\varrho(\mu_1, \mu_2)$, and p. 305
    ("$\varrho(\mu_1, \mu_2)$ is irreducible unless $\mu_1 \cdot \mu_2^{-1} = \alpha_k$ or $\alpha_k^{-1}$, where $\alpha_k$ is the
    quasi-character of $k^\times \colon x \to \lvert x \rvert$", "The representation $\varrho(\mu_1, \mu_2)$ is said to be in the principal
    series if irreducible", and its central character $\mu_1 \cdot \mu_2$);
  - §2, Theorem 2, p. 307 (two representations of $\mathcal{H}_\mathbb{A}$ occurring in $\mathcal{A}$ that agree at almost all places
    are equal);
  - §3, p. 312: the image of $\mathfrak{S}(k, N, \varepsilon)$ lies in the space $\mathcal{A}_0$ of Jacquet–Langlands, which "is a
    discrete direct sum of irreducible $\mathrm{GL}_2(A)$ representations, each occurring with multiplicity one ([4],
    Proposition 11.1)", and the forms equivalent in the sense of Atkin–Lehner lie in one irreducible representation;
    p. 313, Theorem 4 ("Let $\mathfrak{c}(\pi)$ be the integral ideal whose divisor at each prime $p$ is $\mathfrak{c}(\pi_p)$.
    Then, for integers $N$ not divisible by $\mathfrak{c}(\pi)$, the dimension of $\mathfrak{S}(N, \pi)$ is $0$. In general, if
    $N = \mathfrak{c}(\pi) \cdot \prod p_i^{n_i}$, then the dimension of $\mathfrak{S}(N, \pi)$ is $\prod (n_i + 1)$."), with the sentence after
    it: "In particular, if $N = \mathfrak{c}(\pi)$, then the dimension is exactly one, and the corresponding modular form is
    what Atkin and Lehner call a newform. All newforms arise in this way".
- H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", *Current Developments in Mathematics* 1 (1995),
  International Press; page numbers of the authors' text at
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: §1.2, pp. 26–27 (the Petersson scalar
  product and the diamond operators), §1.3, pp. 28–29 (the operators $T_p$ and $U_q$), Definition 1.21 and Theorem 1.22,
  p. 31 (old and new subspaces, newforms of level $N$, and the decomposition $S_2(\Gamma) = \oplus_f S_f$), and §3.1,
  p. 84 (the character $\psi_f$ of a newform).
