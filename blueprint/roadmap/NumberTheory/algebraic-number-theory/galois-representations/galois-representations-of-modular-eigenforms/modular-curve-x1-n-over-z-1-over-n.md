# The modular curve X₁(N) over Z[1/N]

This node is still to be broken down. It covers the integral model of the modular curve $X_1(N)$ that the
Eichler–Shimura construction reduces modulo primes $p \nmid N$, in the form in which Conrad uses it.

Let $N \ge 5$. For a $\mathbb{Z}[1/N]$-scheme $S$, an elliptic curve $E \to S$ is a proper smooth group
scheme with geometrically connected fibres of dimension $1$, and a point of exact order $N$ on $E$ is a
section $P \colon S \to E$ that is killed by $N$ and has order $N$ on every geometric fibre. Then:

1. there is a smooth affine $\mathbb{Z}[1/N]$-scheme $Y_1(N)$ with a pair $(\mathcal{E}, \mathcal{P})$ over it
   that is universal for elliptic curves with a point of exact order $N$: for every $\mathbb{Z}[1/N]$-scheme $S$,
   pulling back $(\mathcal{E}, \mathcal{P})$ gives a bijection, functorial in $S$, from the morphisms
   $S \to Y_1(N)$ to the isomorphism classes of pairs $(E, P)$ over $S$;
2. $Y_1(N)$ is an open subscheme of a proper smooth $\mathbb{Z}[1/N]$-scheme $X_1(N)$ of relative dimension $1$
   with geometrically connected fibres, which has a finite flat map to $\mathbb{P}^1_{\mathbb{Z}[1/N]}$ under which
   $Y_1(N)$ is the preimage of $\mathbb{A}^1_{\mathbb{Z}[1/N]} = \mathbb{P}^1_{\mathbb{Z}[1/N]} - \{\infty\}$;
3. there is an isomorphism of $X_1(N) \times_{\mathbb{Z}[1/N]} \mathbb{C}$, as a compact Riemann surface, with
   $X_1(N)^{\mathrm{an}}$, the compactification of $\Gamma_1(N) \backslash \mathfrak{H}$, under which the class of
   $\tau \in \mathfrak{H}$ is the point of $Y_1(N)(\mathbb{C})$ given by the pair
   $\bigl(\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau),\ 1/N\bigr)$.

So for every prime $p \nmid N$ the fibre $X_1(N)_{\mathbb{F}_p}$ is a proper smooth geometrically connected curve
over $\mathbb{F}_p$: the modular curve has good reduction at $p$.

## Depends on

- [Congruence subgroup $\Gamma_1(N)$](../../../modular-forms-q-series/modular-forms/congruence-subgroup-gamma1.md), for $\Gamma_1(N) \backslash \mathfrak{H}$

## Proof depends on

Its proof uses the inputs listed in the expansion note.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the representability of the moduli problem of elliptic curves with a point of exact order $N$ over
  $\mathbb{Z}[1/N]$ for $N \ge 4$ by a smooth affine curve with irreducible geometric fibres (Igusa;
  Diamond–Im, Theorem 8.2.1, deduced there from Katz–Mazur (2.7.3), (3.7.1) and (4.7.1));
- the compactification by generalized elliptic curves (Deligne–Rapoport), which gives the proper smooth curve
  $X_1(N)$ over $\mathbb{Z}[1/N]$ (Diamond–Im, §9.3, with Theorem 9.3.7 for the variant $X_\mu(N)$ that uses
  embeddings of $\mu_N$);
- the comparison of the complex fibre with $X_1(N)^{\mathrm{an}}$, through the moduli interpretation of
  $\Gamma_1(N) \backslash \mathfrak{H}$ by the pairs $\bigl(\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau), 1/N\bigr)$, and the
  geometric connectedness of the fibres, which it reduces to the connectedness of $X_1(N)^{\mathrm{an}}$;
- the curve $X_1(N, p)$ over $\mathbb{Z}[1/Np]$ for triples $(E, P, C)$ with $C$ a finite locally free subgroup
  scheme of order $p$, and the extension of the maps $\pi_1(E, P, C) = (E, P)$,
  $\pi_2(E, P, C) = (E/C, P \bmod C)$ and $I_n(E, P) = (E, nP)$ to the compactifications, which Conrad
  derives from the theory of minimal regular proper models (p. 67).

## Sources

- B. Conrad, "The Shimura construction in weight 2", appendix to K. A. Ribet and W. A. Stein,
  *Lectures on Serre's conjectures*, IAS/Park City Mathematics Series; page numbers are those of the
  authors' text at <https://wstein.org/edu/Fall2003/252/references/ribet-stein-serre/ribet-stein.pdf>:
  §5.2, pp. 66–67 (elliptic curves and points of exact order $N$ over a $\mathbb{Z}[1/N]$-scheme; "for
  $N \ge 5$ there is a proper smooth $\mathbb{Z}[\frac{1}{N}]$-scheme $X_1(N)$ equipped with a finite flat map
  to $\mathbb{P}^1_{\mathbb{Z}[\frac{1}{N}]}$" with $Y_1(N)$ the base of a universal object; the geometric
  connectedness of the fibres through the comparison with $X_1(N)^{\mathrm{an}}$; the curve $X_1(N, p)$ and the
  maps $\pi_1^{(p)}$, $\pi_2^{(p)}$, $I_n$), citing Katz–Mazur and Deligne–Rapoport, which were not read for
  this page.
- F. Diamond and J. Im, "Modular forms and modular curves", Canadian Mathematical Society Conference
  Proceedings 17 (1995), cited by section, theorem and equation numbers: §8.2, Theorem 8.2.1 ("If $N > 3$,
  then there is a scheme $Y_1(N)$ which represents the functor $F_1(N)$. Moreover $Y_1(N)$ is smooth of relative
  dimension one over $\mathbb{Z}[1/N]$ with irreducible geometric fibers", with "The proof is essentially due to
  Igusa"); §9.3, Variant 9.3.6 and Theorem 9.3.7.
- H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", page numbers of the authors' text at
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: §1.5, p. 35 ("Models over
  $\mathbf{Z}$": the curve "has good reduction at primes $p$ not dividing $N$", citing Igusa, Deligne–Rapoport,
  Drinfeld and Katz–Mazur).
- F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228, Springer
  (2005): §8.6, "Modular curves in characteristic $p$: Igusa's Theorem", p. 347, from the table of contents;
  the section itself was not read.
