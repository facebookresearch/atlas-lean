# Carayol's theorem on the ℓ-adic representations of Hilbert modular forms

Let $F$ be a totally real number field of degree $d$ with real embeddings $\tau_1, \dots, \tau_d$. For integers
$k \ge 2$ and $w$ of the same parity, let $D_{k,w}$ be the essentially square-integrable representation of
$\mathrm{GL}_2(\mathbb{R})$ that occurs in the unitarily induced representation $\mathrm{Ind}(\mu, \nu)$ of the
characters

$$\mu(t) = \lvert t \rvert^{(k - 1 - w)/2} \operatorname{sgn}(t)^k, \qquad \nu(t) = \lvert t \rvert^{(-k + 1 - w)/2}$$

of $\mathbb{R}^\times$; its central character is $\mu\nu \colon t \mapsto t^{-w}$. Let $k_1, \dots, k_d \ge 2$ and $w$ be
integers of the same parity, and let $\pi = \bigotimes_v \pi_v$ be a cuspidal automorphic representation of
$\mathrm{GL}_2(\mathbb{A}_F)$ with $\pi_{\tau_i} \cong D_{k_i, w}$ for $i = 1, \dots, d$, such that, if $d$ is even, the
local component $\pi_v$ at some finite place $v$ is essentially square-integrable (special or cuspidal). Such
representations correspond to holomorphic Hilbert modular forms of weight $(k_1, \dots, k_d)$. For each finite place
$\mathfrak{p}$ of $F$ let $\sigma(\pi_\mathfrak{p})$ be the Weil–Deligne representation of $W_{F_\mathfrak{p}}$ attached to
$\pi_\mathfrak{p}$ by [Carayol's Hecke correspondence](carayol-s-hecke-correspondence.md). There is a number field
$\mathbb{Q}(\pi)$ over which all the $\pi_\mathfrak{p}$ are defined, and a finite extension of it over which all the
$\sigma(\pi_\mathfrak{p})$ are realized; for such a field $E$ and a finite place $\lambda$ of $E$ whose residue
characteristic differs from that of $\mathfrak{p}$, let $\sigma^\lambda(\pi_\mathfrak{p})$ be the $\lambda$-adic realization of
$\sigma(\pi_\mathfrak{p})$, a continuous representation of $W_{F_\mathfrak{p}}$.

**Theorem (Carayol, Théorème (A)).** There are a finite extension $E$ of $\mathbb{Q}(\pi)$ and a strictly compatible
system $\{\sigma^\lambda\}$ of continuous two-dimensional $E_\lambda$-adic representations of
$\operatorname{Gal}(\overline{F}/F)$ such that, for every finite place $\mathfrak{p}$ of $F$ and every finite place $\lambda$
of $E$ whose residue characteristic differs from that of $\mathfrak{p}$, the restriction $\sigma^\lambda_\mathfrak{p}$ of
$\sigma^\lambda$ to the local Weil group $W_{F_\mathfrak{p}}$ is equivalent to $\sigma^\lambda(\pi_\mathfrak{p})$.

The restriction to $W_{F_\mathfrak{p}}$ is taken through a decomposition group at $\mathfrak{p}$. Carayol notes that the
existence of a system with this property at almost every finite place was known before, and that the new result is
the determination of $\sigma^\lambda_\mathfrak{p}$ at every finite place. The case $F = \mathbb{Q}$, $k_1 = 2$ is the one
used for the [conductor of the ℓ-adic representation of a newform](conductor-of-the-l-adic-representation-of-a-weight-two-newform.md).

## Expansion

This node is still to be broken down. A good expansion states and links:

1. Carayol's Théorème (B), p. 411: with, when $d$ is even, a fixed finite place $v$ at which $\pi_v$ is essentially
   square-integrable, there are $E$ and a strictly compatible system $\{\sigma^\lambda\}$ satisfying the conclusion of
   Théorème (A) at every finite place $\mathfrak{p} \ne v$ at which $\pi_\mathfrak{p}$ is not extraordinary cuspidal, that is,
   does not correspond to a primitive two-dimensional representation of the Weil group, which happens only in residue
   characteristic $2$ (§0.9, p. 411);
2. the reduction of Théorème (B), through the Jacquet–Langlands correspondence, to Théorème (B′) for the
   quaternion algebra $B$ over $F$ split at $\tau_1$, ramified at $\tau_2, \dots, \tau_d$ and split at every finite
   place except $v$ when $d$ is even (§0.10, p. 412), and the construction of $\{\sigma^\lambda\}$ in the $\ell$-adic
   cohomology of the Shimura curves of $B$ with coefficients in $\ell$-adic sheaves (§0.11, p. 412), along Carayol's
   plan (pp. 412–413): the results of his study of the reduction of Shimura curves (§1, for $F \ne \mathbb{Q}$, the case
   $F = \mathbb{Q}$ being that of the usual modular curves), the construction of the system (§2), torsion and
   determinant (§3), the exact sequence of vanishing cycles (§4), the cohomology of the normalized special fibre and
   the computation of §6 (§§5–6), supersingular divisible $\mathcal{O}$-modules of height $2$ and the universal
   deformation with level structure (§§7–8), the supersingular orbit and the fundamental local representation
   (§§9–10), and the proof of Théorème (B) (§11). For $F = \mathbb{Q}$ Carayol attributes Théorème (B′) to Deligne,
   after Langlands (p. 412; not read here);
3. the base change for $\mathrm{GL}(2)$ along extensions of degree at most $3$ (§12.2, after Langlands and
   Jacquet–Piatetski-Shapiro–Shalika; not read here), with the Proposition of §12.2.2 that the lift of an extraordinary
   cuspidal representation corresponds to the restriction of its Weil group representation, proved in §12.2.3 by a
   global argument, and the lemma of §12.1.3;
4. the proof of Théorème (A) in §12.3, pp. 458–459: at an extraordinary cuspidal place $\mathfrak{p} \ne v_0$ (§12.3.1),
   a totally real cubic extension $L/F$ with a single place $\mathfrak{p}'$ over $\mathfrak{p}$, over which $\sigma(\pi_\mathfrak{p})$
   becomes monomial, Théorème (B) for the lift of $\pi$ to $L$, the [Chebotarev density theorem](../adeles-class-field-theory/chebotarev-density-theorem.md)
   and the equality of determinants (§5.6.1); and, when $d$ is even and $v$ is the only finite place where $\pi_v$ is
   essentially square-integrable, the place $\mathfrak{p} = v$ by a totally real quadratic extension split at $v$
   (§12.3.2).

## Depends on

- [Automorphic forms, cusp forms and automorphic representations](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/automorphic-forms-and-automorphic-representations.md), for cuspidal automorphic representations of $\mathrm{GL}_2(\mathbb{A}_F)$
- [Tensor product theorem for automorphic representations](../../../RepresentationTheory/automorphic-representations/automorphic-forms-on-reductive-groups/tensor-product-theorem.md), for the local components $\pi_v$
- [Discrete series representations and formal degrees](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/discrete-series-and-formal-degrees.md), for the essentially square-integrable representations $D_{k,w}$ of $\mathrm{GL}_2(\mathbb{R})$
- [Characters, principal series and the Langlands classification for real reductive groups](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-real-reductive-groups/principal-series-of-real-reductive-groups.md), for the unitarily induced representations $\mathrm{Ind}(\mu, \nu)$ of $\mathrm{GL}_2(\mathbb{R})$
- [Essentially square-integrable representations of GLₙ](../../../RepresentationTheory/reductive-groups-over-local-fields/representations-of-p-adic-gl-n/essentially-square-integrable-representations-of-gl-n.md), for the essentially square-integrable local components at finite places
- [Carayol's Hecke correspondence for GL₂](carayol-s-hecke-correspondence.md), for $\sigma(\pi_\mathfrak{p})$ and its $\lambda$-adic realizations
- [Weil group of a p-adic field](weil-deligne-representations/weil-group-of-a-p-adic-field.md), for the local Weil groups $W_{F_\mathfrak{p}}$

## Proof depends on

- [Chebotarev density theorem](../adeles-class-field-theory/chebotarev-density-theorem.md), for the comparison of the restriction of $\sigma^\lambda$ to $\operatorname{Gal}(\overline{F}/L)$ with the representation attached to the lift of $\pi$ to $L$ (expansion item 4)

## Sources

- H. Carayol, "Sur les représentations $l$-adiques associées aux formes modulaires de Hilbert", Ann. Sci. École
  Norm. Sup. (4) 19 (1986), no. 3, 409–468, doi:10.24033/asens.1512:
  - §§0.1–0.3, p. 409: $F$, $\tau_1, \dots, \tau_d$, $D_{k,w}$ in $\mathrm{Ind}(\mu, \nu)$ (induction unitaire) with
    $\mu(t) = \lvert t \rvert^{(1/2)(k-1-w)}.\operatorname{sgn}(t)^k$, $\nu(t) = \lvert t \rvert^{(1/2)(-k+1-w)}$ and central
    character $t \to t^{-w}$, the representations $\pi$ with $\pi_{\tau_i} \simeq D_{k_i, w}$ (cf. [Oh]), and the
    hypothesis for $d$ even;
  - §§0.5–0.6, p. 410: the Hecke correspondence, $\mathbb{Q}(\pi)$ (citing [W]), $E$ and the realizations
    $\sigma^\lambda(\pi_\mathfrak{p})$;
  - §0.7, pp. 410–411: Théorème (A), "Soit $\pi$ comme en (0.3). Il existe alors une extension finie $E$ de $\mathbb{Q}(\pi)$
    et un système strictement compatible $\{\sigma^\lambda\}$ de représentations continues $E_\lambda$-adiques de dimension 2
    du groupe de Galois $\operatorname{Gal}(\overline{F}/F)$, vérifiant la propriété suivante : pour toute place finie
    $\mathfrak{p}$ de $F$, et pour toute place finie $\lambda$ de $E$, de caractéristique résiduelle différente de celle de
    $\mathfrak{p}$, la restriction $\sigma^\lambda_\mathfrak{p}$ de $\sigma^\lambda$ au groupe de Weil local $W_{F_\mathfrak{p}}$ est
    équivalente à $\sigma^\lambda(\pi_\mathfrak{p})$.", the paragraph after it ("L'existence du système $\{\sigma^\lambda\}$
    vérifiant la propriété du théorème pour *presque toute* place finie $\mathfrak{p}$ était déjà connue : cf. [Oh],
    [R.T]") and the Remarque (irreducibility, after Ribet, unpublished);
  - §§0.9–0.11, pp. 411–412: Théorèmes (B) and (B′), the quaternion algebra $B$, the Shimura curves, and the
    attribution of the case $F = \mathbb{Q}$ to Deligne after Langlands; the plan, pp. 412–413, and §1, p. 413
    ("Le corps $F$ est supposé distinct de $\mathbb{Q}$ (le cas $F = \mathbb{Q}$ correspond à la théorie classique des
    courbes modulaires usuelles)");
  - §12.2, pp. 457–458: the cubic base change for $\mathrm{GL}_2$ (§12.2.1, after Langlands [L.2] and
    Jacquet–Piatetski-Shapiro–Shalika [J.P.S.S.]), the Proposition of §12.2.2, for an extension $L/F$ of degree at
    most $3$ of $p$-adic fields and an extraordinary cuspidal $\pi$ with Weil group representation $\sigma$ ("Alors le
    relèvement $\Pi = \pi_{L/F}$ correspond à la restriction $\Sigma$ de $\sigma$ au groupe $W_L$."), the Remarque
    replacing the Langlands correspondence by the Hecke correspondence there, and the proof, §12.2.3;
  - §12.3, pp. 458–459: the proof of Théorème (A), using the lemma of §12.1.3.
- H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", *Current Developments in Mathematics* 1 (1995),
  International Press; page numbers of the authors' text at
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>, p. 87: parts (d) and (e) of their
  Theorem 3.1 "follow from a deep result of Carayol [Ca1], Thm. (A), building on the work of Langlands [Ll1],
  Deligne and others".
