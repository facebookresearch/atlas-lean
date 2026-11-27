# Casselman's theorem on local newforms for GL₂

Let $F$ be a finite extension of $\mathbb{Q}_p$ with ring of integers $\mathcal{O}$, maximal ideal $\mathfrak{p}$ and
residue field of $q$ elements, and for an ideal $\mathfrak{b}$ of $\mathcal{O}$ let

$$\Gamma_0(\mathfrak{b}) = \left\{ \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{GL}_2(\mathcal{O}) :
c \equiv 0 \pmod{\mathfrak{b}} \right\}.$$

Let $\varrho$ be an irreducible admissible infinite-dimensional representation of $\mathrm{GL}_2(F)$ on a space $V$,
and $\epsilon$ the quasi-character of $F^\times$ with $\varrho = \epsilon$ on the scalar matrices. For an integer
$n \ge 0$ let $V(\mathfrak{p}^n) \subseteq V$ be, for $n = 0$, the space of vectors fixed by $\mathrm{GL}_2(\mathcal{O})$, and,
for $n \ge 1$, the space of vectors $v$ with

$$\varrho\begin{pmatrix} a & b \\ c & d \end{pmatrix} v = \epsilon(a)\, v \qquad \text{for all }
\begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \Gamma_0(\mathfrak{p}^n);$$

for $n \ge 1$ the entry $a$ of such a matrix is a unit, as $ad - bc$ is a unit and $c \in \mathfrak{p}$.
**Casselman's theorem**: there is a largest ideal $\mathfrak{c}(\varrho) = \mathfrak{p}^{\delta(\varrho)}$ of $\mathcal{O}$ with
$V(\mathfrak{c}(\varrho)) \neq 0$, and $V(\mathfrak{c}(\varrho))$ has dimension one. More generally,
$V(\mathfrak{c}(\varrho)\mathfrak{p}^i)$ has dimension $i + 1$ for every $i \ge 0$. The ideal $\mathfrak{c}(\varrho)$ is the
**conductor** of $\varrho$, and its exponent is that of the $\varepsilon$-factor of $\varrho$: for a nontrivial additive character $\psi$ of $F$,
with $c(\psi)$ the largest integer $r$ such that $\psi$ is trivial on $\mathfrak{p}^{-r}$,

$$\varepsilon(\varrho, \psi, s) = \varepsilon(\varrho, \psi, 0)\, q^{-s(\delta(\varrho) + 2c(\psi))},$$

so that $\delta(\varrho)$ is the exponent of the $\varepsilon$-factor of $\varrho$.

At level $\mathcal{O}$ the group $\Gamma_0(\mathcal{O})$ is all of $\mathrm{GL}_2(\mathcal{O})$, whose entry $a$ need not be a unit,
and Casselman's condition (1.1) is read there as invariance under $\mathrm{GL}_2(\mathcal{O})$, as his proof and his
application to modular forms read it and as Wedhorn's $K_2(0) = \mathrm{GL}_2(\mathcal{O})$ gives it. With the
transformation law at level $\mathcal{O}$ the statement would fail: for the spherical vector of
$\mathrm{Ind}(\lvert \cdot \rvert, \lvert \cdot \rvert)$, whose central character is $\lvert \cdot \rvert^2$, the matrix
$\left(\begin{smallmatrix} \varpi & 1 \\ 1 & 0 \end{smallmatrix}\right) \in \mathrm{GL}_2(\mathcal{O})$, for a uniformizer $\varpi$, fixes
the vector instead of multiplying it by $\lvert \varpi \rvert^2$.

## Expansion

This node is still to be broken down. A good expansion states and links:

1. the absolutely cuspidal case, in the Kirillov model of $\varrho$ on Schwartz–Bruhat functions on $F^\times$ for an
   additive character with conductor $\mathcal{O}$, through the operator $\varrho(w)$, $w = \left(\begin{smallmatrix} 0 & 1 \\
   -1 & 0 \end{smallmatrix}\right)$, written with the monomials $C_0(\nu) t^{n_\nu}$ of Jacquet–Langlands, and the lemma
   reducing the conditions for $\Gamma_0(\mathfrak{p}^m)$ to the Borel subgroup and the element
   $\left(\begin{smallmatrix} 0 & 1 \\ -\pi^m & 0 \end{smallmatrix}\right)$ (Casselman, pp. 302–304), which gives
   $\mathfrak{c}(\varrho) = (\pi^{-n_1})$ and the dimensions $m + n_1 + 1$;
2. the principal series $\rho(\mu_1, \mu_2)$, through the restriction to $\mathrm{GL}_2(\mathcal{O})$ and the double cosets
   of the Borel subgroup, with $\mathfrak{c}(\varrho)$ the product of the conductors of $\mu_1$ and $\mu_2$, and the special
   representations $\sigma(\mu\alpha^{1/2}, \mu\alpha^{-1/2})$, with $\mathfrak{c}(\varrho) = (\text{conductor of } \mu)^2$ for
   ramified $\mu$ and $\mathfrak{p}$ for unramified $\mu$ (pp. 304–306);
3. the identification of $\mathfrak{c}(\varrho)$ with the ideal $\mathfrak{p}^\delta$ read off the $\varepsilon$-factor, by comparison
   with Jacquet–Langlands (Remark, pp. 306–307, which states it without proof), using the
   [L- and ε-factors](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/l-and-epsilon-factors-of-pairs.md)
   of $\varrho$.

## Depends on

- [Smooth and admissible representations of p-adic groups](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/smooth-representations-of-p-adic-groups.md), for irreducible admissible representations and central characters
- [L- and ε-factors of pairs for GLₙ and of Weil–Deligne representations](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/l-and-epsilon-factors-of-pairs.md), for $\varepsilon(\varrho, \psi, s)$

## Proof depends on

- [Mirabolic restriction and Bernstein–Zelevinsky derivatives](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/bernstein-zelevinsky-derivatives.md), for the Kirillov model of an infinite-dimensional irreducible representation of $\mathrm{GL}_2(F)$ (expansion item 1)
- [Parabolic induction and Jacquet functors](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-reductive-groups/parabolic-induction-and-jacquet-functors.md), for the principal series $\varrho(\mu_1, \mu_2)$ on the induced space $\mathcal{B}(\mu_1, \mu_2)$ of functions on $\mathrm{GL}_2(F)$ (Casselman, p. 304), whose vectors of level $\mathfrak{p}^n$ are computed through the restriction to $\mathrm{GL}_2(\mathcal{O})$ and the double cosets of the Borel subgroup (expansion item 2)

## Sources

- W. Casselman, "On some results of Atkin and Lehner", Math. Ann. 201 (1973), 301–314, §1, "The Local Result",
  for any locally compact non-archimedean field $k$:
  - Theorem 1, p. 302: for $\varrho$ irreducible admissible infinite-dimensional with central quasi-character
    $\varepsilon$, $\mathfrak{c}(\varrho)$ is the largest ideal of $\mathfrak{o}_k$ for which the space of vectors satisfying
    condition (1.1), $\varrho(g) v = \varepsilon(a) v$ on $\Gamma_0(\mathfrak{c}(\varrho))$, is not empty; "Then this space has
    dimension one. (As we shall see, the ideal $\mathfrak{c}(\varrho)$ may reasonably be called the conductor of
    $\varrho$.)";
  - the proof, pp. 302–306 (the Lemma on p. 303, the absolutely cuspidal case, pp. 302–304, the principal series and
    the special representations, pp. 304–306), which treats the whole of $\mathrm{GL}_2(\mathfrak{o}_k)$ through its fixed
    vectors: "First of all, there are none which are fixed by all of $\mathrm{GL}_2(\mathfrak{o}_k)$ ([4], p. 117), so we may
    assume $\mathfrak{c}$ proper" (p. 303), and p. 304 (the space $\mathcal{B}(\mu_1, \mu_2)$ of locally constant $f$ on
    $\mathrm{GL}_2(k)$ with $f\bigl(\left(\begin{smallmatrix} a & x \\ 0 & b \end{smallmatrix}\right) g\bigr) = \mu_1(a) \cdot \mu_2(b) \cdot \lvert a/b \rvert^{1/2} \cdot f(g)$
    and its right regular representation $\varrho(\mu_1, \mu_2)$);
  - Corollary to the Proof, p. 306 ("If in condition (1.1) of Theorem 1 we replace $\mathfrak{c}(\varrho)$ by an ideal
    $\mathfrak{c}(\varrho) \cdot \mathfrak{p}^i$ contained in it, then the dimension of the space satisfying the new condition is
    $(i + 1)$");
  - Remark, pp. 306–307: the factor $\varepsilon(s, \varrho, \psi)$ of Jacquet–Langlands (p. 76 of their book) "will have the
    form $\varepsilon(\varrho, \psi) \cdot N\mathfrak{p}^{(2c(\psi) - \delta)s}$ where $\varepsilon(\varrho, \psi)$ is independent of $s$ and
    $c(\psi)$ is the exponent of the conductor of $\psi$. The ideal $\mathfrak{p}^\delta$ is the same as our
    $\mathfrak{c}(\varrho)$."
  - §3, p. 313: for $p \nmid N$, where $K_p = \mathrm{GL}_2(\mathbb{Z}_p)$, the space $W_p$ of the vectors $u$ with
    $\pi_p(\kappa) u = \varepsilon_p(\kappa) u$ for $\kappa \in K_p$ has dimension one by "the theory of spherical functions and
    class one representations for $\mathrm{GL}_2$".
- T. Wedhorn, "The local Langlands correspondence for GL(n) over p-adic fields", lecture notes,
  arXiv:math/0011210 (version 2), (2.5.4), p. 33: $K_n(t)$, "In particular, we have $K_n(0) = \mathrm{GL}_n(\mathcal{O}_K)$", and
  the conductor as the smallest $t$ with $V^{K_n(t)} \neq (0)$, for fixed vectors.
- C. J. Bushnell, G. Henniart and P. C. Kutzko, "Correspondance de Langlands locale pour $\mathrm{GL}_n$ et
  conducteurs de paires", Ann. Sci. École Norm. Sup. (4) 31 (1998), no. 4, 537–560,
  doi:10.1016/S0012-9593(98)80106-7, §1.3, p. 538 (the exponent $f(\pi)$ of $\varepsilon(\pi, \psi_F, s)$, with $c(\psi_F)$ the
  largest $r$ such that $\psi_F$ is trivial on $\mathfrak{p}_F^{-r}$).
