# Frobenius on the Tate module of J₁(N)

This node is still to be broken down. Let $N \ge 5$ and $\ell$ a prime, let $J$ be the Jacobian of the
[modular curve $X_1(N)$ over $\mathbb{Z}[1/N]$](modular-curve-x1-n-over-z-1-over-n.md) with the Hecke algebra
$\mathbb{T}_1(N)$ acting through the $(\ )_*$-operators of
[Hecke operators on the Jacobian of X₁(N)](hecke-operators-on-the-jacobian-of-x1-n.md), and let
$V_\ell(N) = \mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} \varprojlim_n J[\ell^n](\overline{\mathbb{Q}})$, which is
[free of rank $2$ over $\mathbb{Q}_\ell \otimes \mathbb{T}_1(N)$](tate-module-of-j1-n-is-free-over-the-hecke-algebra.md).
The absolute Galois group $G_{\mathbb{Q}} = \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, with its Krull topology,
acts on the points $J[\ell^n](\overline{\mathbb{Q}})$ and so on $V_\ell(N)$. Then:

1. this action commutes with $\mathbb{T}_1(N)$ and gives a continuous representation
   $\rho_{N,\ell} \colon G_{\mathbb{Q}} \to \operatorname{Aut}_{\mathbb{Q}_\ell \otimes \mathbb{T}_1(N)}(V_\ell(N)) \cong \mathrm{GL}_2(\mathbb{Q}_\ell \otimes_{\mathbb{Z}} \mathbb{T}_1(N))$,
   unramified at every prime $p \nmid N\ell$: for every maximal ideal $\mathfrak{p}$ over $p$ of the integral closure
   $\overline{\mathbb{Z}}$ of $\mathbb{Z}$ in $\overline{\mathbb{Q}}$, the inertia group of $\mathfrak{p}$, the elements of
   $G_{\mathbb{Q}}$ that fix $\mathfrak{p}$ and act trivially on $\overline{\mathbb{Z}}/\mathfrak{p}$, acts trivially;
2. for every prime $p \nmid N\ell$ and every arithmetic Frobenius element $\mathrm{Frob}_p$ at a maximal ideal
   $\mathfrak{p}$ of $\overline{\mathbb{Z}}$ over $p$, that is, every $\sigma \in G_{\mathbb{Q}}$ with
   $\sigma(x) \equiv x^p \pmod{\mathfrak{p}}$ for all $x \in \overline{\mathbb{Z}}$, the characteristic polynomial of $\rho_{N,\ell}(\mathrm{Frob}_p)$ over
   $\mathbb{Q}_\ell \otimes_{\mathbb{Z}} \mathbb{T}_1(N)$ is

    $$X^2 - (T_p)_* X + p \langle p \rangle_*.$$

## Depends on

- [Hecke operators on the Jacobian of X₁(N) over Z[1/N]](hecke-operators-on-the-jacobian-of-x1-n.md), for $J$, $\mathbb{T}_1(N)$, $(T_p)_*$ and $\langle p \rangle_*$
- [The rational Tate module of J₁(N) is free of rank two over the Hecke algebra](tate-module-of-j1-n-is-free-over-the-hecke-algebra.md), for $V_\ell(N)$ and the coordinates in $\mathrm{GL}_2(\mathbb{Q}_\ell \otimes \mathbb{T}_1(N))$

## Proof depends on

- [Eichler–Shimura relation for X₁(N)](eichler-shimura-relation-for-x1-n.md), for $(T_p)_* = F + \langle p \rangle_* F^\vee$, $F F^\vee = p$ and $w_\zeta^{-1} F w_\zeta = \langle p \rangle_*^{-1} F$ on $J_{\mathbb{F}_p}$
- [The rational Tate module of J₁(N) is free of rank two over the Hecke algebra](tate-module-of-j1-n-is-free-over-the-hecke-algebra.md), for freeness, the Gorenstein property and the self-adjointness of $\mathbb{T}_1(N)$ for $(x, w_\zeta y)_\ell$
- [Characteristic polynomial of the dual of a linear endomorphism](characteristic-polynomial-of-the-dual-endomorphism.md), for $\operatorname{tr}(F) = \operatorname{tr}(\langle p \rangle_* F^\vee)$ on $V_\ell(J_{\mathbb{F}_p})$
- [Néron model of an abelian variety](../../../../AlgebraicGeometry/abelian-varieties/neron-model.md), for good reduction and the Néron–Ogg–Shafarevich criterion of its expansion note, which give the unramifiedness of $V_\ell(N)$ at $p \nmid N\ell$, where $J$ has good reduction

## Expansion

This node is still to be broken down. A good expansion states and links, following Conrad (Lemma 5.11 and
§5.3, pp. 69–71):

- the identification $V_\ell(J_{\mathbb{Q}}) \cong V_\ell(J_{\mathbb{F}_p})$ for $p \nmid N\ell$, through the finite étale group
  schemes $J[\ell^n]$ over $\mathbb{Z}_p$ (Serre–Tate, Lemma 2, as cited by Diamond–Im, §12.5), under which
  $\mathrm{Frob}_p$ acts as the Frobenius endomorphism $F$ of $J_{\mathbb{F}_p}$, compatibly with $\mathbb{T}_1(N)$ and with
  Weil pairings;
- the independence of the choice of $\mathfrak{p}$ and of $\mathrm{Frob}_p$: $G_{\mathbb{Q}}$ permutes the maximal ideals over $p$
  transitively, two arithmetic Frobenius elements at $\mathfrak{p}$ differ by an element of its inertia group, and
  $\rho_{N,\ell}$ commutes with $\mathbb{T}_1(N)$, so the characteristic polynomial does not change under conjugation;
- the Weil pairing of an abelian variety with respect to a polarization, and the fact that the adjoint of an
  endomorphism for it is the dual endomorphism;
- the argument: $F^2 - (T_p)_* F + p \langle p \rangle_* = 0$ from the Eichler–Shimura relation and
  $F F^\vee = p$; the identification $V_\ell(J_{\mathbb{F}_p}) \cong V_\ell(J_{\mathbb{F}_p})^*$ by $(x, w_\zeta y)_\ell$, which takes
  $F$ to $\langle p \rangle_* F^\vee$, so that $\operatorname{tr}(F) = \operatorname{tr}(\langle p \rangle_* F^\vee)$ by the lemma on dual
  endomorphisms; and $2 (T_p)_* = \operatorname{tr}(F + \langle p \rangle_* F^\vee) = 2 \operatorname{tr}(F)$, which with Cayley–Hamilton
  fixes the characteristic polynomial.

## Sources

- B. Conrad, "The Shimura construction in weight 2", appendix to K. A. Ribet and W. A. Stein,
  *Lectures on Serre's conjectures*, IAS/Park City Mathematics Series; page numbers are those of the
  authors' text at <https://wstein.org/edu/Fall2003/252/references/ribet-stein-serre/ribet-stein.pdf>:
  §5.2, Lemma 5.11, p. 68 ("$\rho_{N,\ell} \colon G_{\mathbf{Q}} \to \operatorname{Aut}(V_\ell(N)) \cong \mathrm{GL}(2, \mathbf{Q}_\ell \otimes \mathbf{T}_1(N))$
  is a continuous representation, unramified at $p \nmid N\ell$"), with (5.6) and "unramified at all $p \nmid N\ell$
  (via Néron-Ogg-Shafarevich)"; Theorem 5.12, p. 68 ("Let $\mathbf{T}_1(N)$ act on
  $\operatorname{Pic}^0_{X_1(N)/\mathbf{Z}[\frac{1}{N}]}$ via the $(\ )_*$-action. For any $p \nmid N\ell$, the characteristic
  polynomial of $\rho_{N,\ell}(\mathrm{Frob}_p)$ is $X^2 - (T_p)_* X + p \langle p \rangle_*$ relative to the
  $\mathbf{Q}_\ell \otimes \mathbf{T}_1(N)$-module structure on $V_\ell(N)$, where $\mathrm{Frob}_p$ denotes an arithmetic
  Frobenius element at $p$"); §5.3, proof of Theorem 5.12 from Theorem 5.16, pp. 69–71.
- H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", page numbers of the authors' text at
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: §1.6, Theorem 1.41 and its proof,
  pp. 42–43 ("For $p$ not dividing $N\ell$, the characteristic polynomial of $F$ on the $\mathbf{T}_{\mathbf{Q}_\ell}$-module
  $\mathbf{V}$ is $X^2 - T_p X + \langle p \rangle p$").
- F. Diamond and J. Im, "Modular forms and modular curves", Canadian Mathematical Society Conference
  Proceedings 17 (1995), cited by section and equation numbers: §12.5, (12.5.4) and the surrounding argument
  (the étale group schemes $\mathcal{J}[\ell^n]_{\mathbf{Z}_p}$, citing Serre–Tate, Lemma 2; "One can use the Weil pairing
  to show that $\mathrm{Frob}_p$ and $\langle p \rangle p \mathrm{Frob}_p^{-1}$ have the same trace").
- J.-P. Serre and J. Tate, "Good reduction of abelian varieties", Ann. of Math. 88 (1968), 492–517: Lemma 2, as
  cited by Diamond–Im, §12.5; not read for this page.
