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
[Galois representations attached to normalized eigenforms](../../not-yet-classified/exists-galois-rep-charpoly-frob.md). Then there is a cuspidal automorphic representation
$\pi = \bigotimes_v \pi_v$ of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ such that:

1. $\pi_\infty \cong D_{2,0}$, the representation of $\mathrm{GL}_2(\mathbb{R})$ in the
   [discrete series](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/discrete-series-and-formal-degrees.md), with trivial central character, that occurs in the
   [unitarily induced representation](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/principal-series-of-real-reductive-groups.md)
   $\mathrm{Ind}(\mu, \nu)$ of the characters $\mu(t) = \lvert t \rvert^{1/2}$ and $\nu(t) = \lvert t \rvert^{-1/2}$ of
   $\mathbb{R}^\times$ (Carayol's $D_{k,w}$ with $k = 2$ and $w = 0$);
2. for every prime $p \nmid N$, $\pi_p \cong \mathrm{Ind}(\xi_1, \xi_2)$ for unramified characters $\xi_1, \xi_2$ of
   $\mathbb{Q}_p^\times$ such that $\xi_1(p)p^{1/2}$ and $\xi_2(p)p^{1/2}$ are the roots of $X^2 - a_p X + \psi(p)\,p$, where
   $\mathrm{Ind}(\xi_1, \xi_2)$ is the [normalized parabolic induction](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md)
   from the upper triangular Borel subgroup of the character
   $\left(\begin{smallmatrix} a & 0 \\ 0 & b \end{smallmatrix}\right) \mapsto \xi_1(a)\xi_2(b)$ of the diagonal torus: the
   smooth functions $\phi$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ with
   $\phi\bigl(\left(\begin{smallmatrix} a & x \\ 0 & b \end{smallmatrix}\right) g\bigr) = \xi_1(a)\xi_2(b)\lvert a/b \rvert^{1/2} \phi(g)$,
   under right translation;
3. for every prime $p$, the conductor of $\pi_p$ in the sense of
   [Casselman's theorem on local newforms](local-newforms-for-gl-2.md) is $\mathfrak{c}(\pi_p) = p^{v_p(N)}\mathbb{Z}_p$.

## Expansion

This node is still to be broken down. A good expansion states and links:

1. the passage from modular forms to functions on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$: Casselman's map $\Phi$ on the space
   $\mathfrak{S}(k, N, \epsilon)$ of cusp forms with $f|[\gamma]_k = \epsilon(a)^{-1} f$ for $\gamma \in \Gamma_0(N)$, which for $f$ as
   above, with $\langle d \rangle f = \psi(d) f$ and $d \equiv a^{-1} \pmod N$, is the type $\epsilon = \psi$; the
   characterization of its image by the conditions $(\Phi 1)$–$(\Phi 7)$ (Theorem 3, p. 312), the decomposition of the
   image into irreducible representations occurring with multiplicity one, and strong multiplicity one (Theorem 2,
   p. 307);
2. the archimedean component: all forms of weight $k$ have the same component at the real place, by comparison of
   $(\Phi 3)$–$(\Phi 5)$ with the representations of $\mathrm{GL}_2(\mathbb{R})$ of Jacquet–Langlands (Casselman, p. 312),
   which for $k = 2$ and unitary central character is $D_{2,0}$;
3. the normalization of item 2: the eigenvalues of $T_p$ and of the diamond operators on the vector of
   $\mathrm{Ind}(\xi_1, \xi_2)$ fixed by $\mathrm{GL}_2(\mathbb{Z}_p)$, which give $\xi_1(p)p^{1/2} + \xi_2(p)p^{1/2} = a_p$ and
   $\xi_1(p)\xi_2(p) = \psi(p)$; Casselman states only that the eigenvalues determine the local component (p. 312);
4. the conductor: Casselman's Theorem 4, p. 313, by which, with $\mathfrak{c}(\pi)$ the ideal with local components
   $\mathfrak{c}(\pi_p)$, the forms of level $N$ in $\pi$ form a space of dimension $\prod (n_i + 1)$ when
   $N = \mathfrak{c}(\pi) \prod p_i^{n_i}$, and none when $\mathfrak{c}(\pi)$ does not divide $N$, so that a newform of level $N$
   has $\mathfrak{c}(\pi) = N$; with the agreement of the newforms above with those of Atkin and Lehner and of Li, through the
   decomposition of $S_2(\Gamma_1(N))$ along the newforms of levels dividing $N$ (Darmon–Diamond–Taylor, Theorem 1.22,
   citing Atkin–Lehner and Lang, Chapter VIII; not read here).

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for cuspidal automorphic representations of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$
- [Tensor product theorem for automorphic representations](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/tensor-product-theorem.md), for the local components $\pi_v$
- [Hecke operators $T_n$ on weight-two cusp forms for a group of level $N$](../../modular-forms-q-series/modular-forms/hecke-operators-of-level-n.md), for the operators $T_p$ ($p \nmid N$) and $U_q = T_q$ ($q \mid N$) on $S_2(\Gamma_1(N))$
- [Galois representations attached to normalized eigenforms](../../not-yet-classified/exists-galois-rep-charpoly-frob.md), for the nebentypus convention $f \mid_2 \gamma = \psi(d) f$, $\gamma \in \Gamma_0(N)$
- [Discrete series representations and formal degrees](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/discrete-series-and-formal-degrees.md), for the square-integrable representation $D_{2,0}$ of $\mathrm{GL}_2(\mathbb{R})$
- [Casselman's theorem on local newforms for GL₂](local-newforms-for-gl-2.md), for the conductor $\mathfrak{c}(\pi_p)$
- [Characters, principal series and the Langlands classification for real reductive groups](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/principal-series-of-real-reductive-groups.md), for unitary induction $\mathrm{Ind}(\mu, \nu)$ on $\mathrm{GL}_2(\mathbb{R})$
- [Parabolic induction and Jacquet functors](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md), for the normalized induction $\mathrm{Ind}(\xi_1, \xi_2)$ from the upper triangular Borel subgroup of $\mathrm{GL}_2(\mathbb{Q}_p)$

## Proof depends on

- [Casselman's theorem on local newforms for GL₂](local-newforms-for-gl-2.md), for the dimensions of the spaces of vectors of level $\mathfrak{c}(\pi_p)p^i$ behind Casselman's Theorem 4 (expansion item 4)

## Sources

- W. Casselman, "On some results of Atkin and Lehner", Math. Ann. 201 (1973), 301–314:
  - §1, p. 304: for quasi-characters $\mu_1, \mu_2$ of $k^\times$, the space $\mathcal{B}(\mu_1, \mu_2)$ of locally constant
    functions $f$ on $\mathrm{GL}_2(k)$ with $f\bigl(\left(\begin{smallmatrix} a & x \\ 0 & b \end{smallmatrix}\right) g\bigr) =
    \mu_1(a) \cdot \mu_2(b) \cdot \lvert a/b \rvert^{1/2} \cdot f(g)$ and its right regular representation
    $\varrho(\mu_1, \mu_2)$, and p. 305 ("The representation $\varrho(\mu_1, \mu_2)$ is said to be in the principal series if
    irreducible");
  - §2, Theorem 2, p. 307 (two representations of $\mathcal{H}_\mathbb{A}$ occurring in $\mathcal{A}$ that agree at almost all places
    are equal);
  - §3, pp. 309–313: the space $\mathfrak{M}(k, N, \epsilon)$ of forms with "(M 2) $f|[\gamma]_k = \epsilon(a)^{-1} \cdot f$ for all
    $\gamma \in \Gamma_0(N)$", the map $\Phi$ and the conditions $(\Phi 1)$–$(\Phi 7)$, Theorem 3, p. 312, the discussion of the
    components at the real place and at the primes not dividing $N$, p. 312, and Theorem 4, p. 313 ("Let $\mathfrak{c}(\pi)$
    be the integral ideal whose divisor at each prime $p$ is $\mathfrak{c}(\pi_p)$. Then, for integers $N$ not divisible by
    $\mathfrak{c}(\pi)$, the dimension of $\mathfrak{S}(N, \pi)$ is $0$. In general, if $N = \mathfrak{c}(\pi) \cdot \prod p_i^{n_i}$, then the
    dimension of $\mathfrak{S}(N, \pi)$ is $\prod (n_i + 1)$."), with the sentence after it: "In particular, if $N = \mathfrak{c}(\pi)$,
    then the dimension is exactly one, and the corresponding modular form is what Atkin and Lehner call a newform.
    All newforms arise in this way".
- H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", *Current Developments in Mathematics* 1 (1995),
  International Press; page numbers of the authors' text at
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: §1.2, pp. 26–27 (the Petersson scalar
  product and the diamond operators), §1.3, pp. 28–29 (the operators $T_p$ and $U_q$), Definition 1.21 and Theorem 1.22,
  p. 31 (old and new subspaces, newforms of level $N$, and the decomposition $S_2(\Gamma) = \oplus_f S_f$), and §3.1,
  p. 84 (the character $\psi_f$ of a newform).
- H. Carayol, "Sur les représentations $l$-adiques associées aux formes modulaires de Hilbert", Ann. Sci. École
  Norm. Sup. (4) 19 (1986), no. 3, 409–468, doi:10.24033/asens.1512: §0.2, p. 409 ($D_{k,w}$, "la représentation
  essentiellement de carré intégrable du groupe $\mathrm{GL}_2(\mathbb{R})$ qui intervient dans l'induite $\mathrm{Ind}(\mu, \nu)$
  (induction unitaire)", with $\mu(t) = \lvert t \rvert^{(1/2)(k-1-w)} \operatorname{sgn}(t)^k$, $\nu(t) = \lvert t \rvert^{(1/2)(-k+1-w)}$ and
  central character $t \mapsto t^{-w}$) and §0.3, p. 409 (automorphic representations and holomorphic Hilbert modular
  forms, cf. [Oh]).
