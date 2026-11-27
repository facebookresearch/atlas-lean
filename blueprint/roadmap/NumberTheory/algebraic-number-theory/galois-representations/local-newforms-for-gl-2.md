# Casselman's theorem on local newforms for GL₂

Let $F$ be a finite extension of $\mathbb{Q}_p$ with ring of integers $\mathcal{O}$, maximal ideal $\mathfrak{p}$ and
residue field of $q$ elements, and for an ideal $\mathfrak{b}$ of $\mathcal{O}$ let

$$\Gamma_0(\mathfrak{b}) = \left\{ \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{GL}_2(\mathcal{O}) :
c \equiv 0 \pmod{\mathfrak{b}} \right\}.$$

Let $\varrho$ be an irreducible admissible infinite-dimensional representation of $\mathrm{GL}_2(F)$ and $\epsilon$
the quasi-character of $F^\times$ with $\varrho = \epsilon$ on the scalar matrices. **Casselman's theorem**: there is
a largest ideal $\mathfrak{c}(\varrho)$ of $\mathcal{O}$ for which the space of vectors $v$ with

$$\varrho\begin{pmatrix} a & b \\ c & d \end{pmatrix} v = \epsilon(a)\, v \qquad \text{for all }
\begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \Gamma_0(\mathfrak{c}(\varrho))$$

is nonzero, and this space has dimension one. More generally, for the ideal $\mathfrak{c}(\varrho)\mathfrak{p}^i$,
$i \ge 0$, the space of vectors with the same property for $\Gamma_0(\mathfrak{c}(\varrho)\mathfrak{p}^i)$ has
dimension $i + 1$. The ideal $\mathfrak{c}(\varrho) = \mathfrak{p}^{\delta(\varrho)}$ is the **conductor** of $\varrho$,
and its exponent is that of the $\varepsilon$-factor of $\varrho$: for a nontrivial additive character $\psi$ of $F$,
with $c(\psi)$ the largest integer $r$ such that $\psi$ is trivial on $\mathfrak{p}^{-r}$,

$$\varepsilon(\varrho, \psi, s) = \varepsilon(\varrho, \psi, 0)\, q^{-s(\delta(\varrho) + 2c(\psi))},$$

so that $\delta(\varrho)$ is the exponent of the $\varepsilon$-factor of $\varrho$.

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

## Sources

- W. Casselman, "On some results of Atkin and Lehner", Math. Ann. 201 (1973), 301–314, §1, "The Local Result",
  for any locally compact non-archimedean field $k$:
  - Theorem 1, p. 302: for $\varrho$ irreducible admissible infinite-dimensional with central quasi-character
    $\varepsilon$, $\mathfrak{c}(\varrho)$ is the largest ideal of $\mathfrak{o}_k$ for which the space of vectors satisfying
    condition (1.1), $\varrho(g) v = \varepsilon(a) v$ on $\Gamma_0(\mathfrak{c}(\varrho))$, is not empty; "Then this space has
    dimension one. (As we shall see, the ideal $\mathfrak{c}(\varrho)$ may reasonably be called the conductor of
    $\varrho$.)";
  - the proof, pp. 302–306 (the Lemma on p. 303, the absolutely cuspidal case, pp. 302–304, the principal series and
    the special representations, pp. 304–306);
  - Corollary to the Proof, p. 306 ("If in condition (1.1) of Theorem 1 we replace $\mathfrak{c}(\varrho)$ by an ideal
    $\mathfrak{c}(\varrho) \cdot \mathfrak{p}^i$ contained in it, then the dimension of the space satisfying the new condition is
    $(i + 1)$");
  - Remark, pp. 306–307: the factor $\varepsilon(s, \varrho, \psi)$ of Jacquet–Langlands (p. 76 of their book) "will have the
    form $\varepsilon(\varrho, \psi) \cdot N\mathfrak{p}^{(2c(\psi) - \delta)s}$ where $\varepsilon(\varrho, \psi)$ is independent of $s$ and
    $c(\psi)$ is the exponent of the conductor of $\psi$. The ideal $\mathfrak{p}^\delta$ is the same as our
    $\mathfrak{c}(\varrho)$."
- C. J. Bushnell, G. Henniart and P. C. Kutzko, "Correspondance de Langlands locale pour $\mathrm{GL}_n$ et
  conducteurs de paires", Ann. Sci. École Norm. Sup. (4) 31 (1998), no. 4, 537–560,
  doi:10.1016/S0012-9593(98)80106-7, §1.3, p. 538 (the exponent $f(\pi)$ of $\varepsilon(\pi, \psi_F, s)$, with $c(\psi_F)$ the
  largest $r$ such that $\psi_F$ is trivial on $\mathfrak{p}_F^{-r}$).
