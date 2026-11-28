# Eichler–Shimura relation for X₁(N)

This node is still to be broken down. Let $N \ge 5$, let $p$ be a prime not dividing $N$, and let
$J_p = J_{\mathbb{F}_p} = \operatorname{Pic}^0_{X_1(N)_{\mathbb{F}_p}/\mathbb{F}_p}$ be the reduction at $p$ of the
Jacobian $J$ of the [modular curve $X_1(N)$ over $\mathbb{Z}[1/N]$](modular-curve-x1-n-over-z-1-over-n.md),
with the operators $(T_p)_*$, $\langle n \rangle_*$ and $w_\zeta$ of
[Hecke operators on the Jacobian of X₁(N)](hecke-operators-on-the-jacobian-of-x1-n.md) reduced modulo $p$
($w_\zeta$ through a map $\mathbb{Z}[1/N, \zeta_N] \to \overline{\mathbb{F}}_p$). Let
$F \colon J_p \to J_p$ be the absolute Frobenius endomorphism of the abelian variety $J_p$ over
$\mathbb{F}_p$, which is $\operatorname{Alb}(F_{X_1(N)})$ for the absolute Frobenius $F_{X_1(N)}$ of
$X_1(N)_{\mathbb{F}_p}$, and $F^\vee$ its [dual](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md)
for the canonical principal polarization of the Jacobian. Then, in
$\operatorname{End}_{\overline{\mathbb{F}}_p}(J_p)$,

$$(T_p)_* = F + \langle p \rangle_* F^\vee, \qquad w_\zeta^{-1} F w_\zeta = \langle p \rangle_*^{-1} F,$$

and $F F^\vee = F^\vee F = p$.

The first identity is the **Eichler–Shimura congruence relation**: on divisors supported on the ordinary locus it
is the equality $(T_p)_*\bigl((x) - (x')\bigr) = (F + \langle p \rangle_* F^\vee)\bigl((x) - (x')\bigr)$, where for an
ordinary pair $(E, P)$ over $\overline{\mathbb{F}}_p$ the $p + 1$ subgroups of order $p$ of a lift to characteristic
$0$ reduce to the connected subgroup $\mu_p$ once and to the étale subgroup $p$ times.

## Depends on

- [Hecke operators on the Jacobian of X₁(N) over Z[1/N]](hecke-operators-on-the-jacobian-of-x1-n.md), for $J$, $(T_p)_*$, $\langle n \rangle_*$ and $w_\zeta$
- [The modular curve X₁(N) over Z[1/N]](modular-curve-x1-n-over-z-1-over-n.md), for $X_1(N)_{\mathbb{F}_p}$
- [Dual abelian variety](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md), for $F^\vee$
- [Polarization](../../../../AlgebraicGeometry/abelian-varieties/polarization.md), for the canonical principal polarization by which $F^\vee$ is an endomorphism of $J_p$

## Proof depends on

Its proof uses the inputs listed in the expansion note.

## Expansion

This node is still to be broken down. A good expansion states and links, following Conrad's proof of his
Theorem 5.16 (pp. 72–75):

- the reduction to a Zariski-dense set of points of $J_p(\overline{\mathbb{F}}_p)$: the map
  $X_1(N)^g_{\overline{\mathbb{F}}_p} \to J_{p,\overline{\mathbb{F}}_p}$ from an $\mathbb{F}_p$-rational base point is surjective, so
  differences $(x) - (x')$ of points of the ordinary locus of $Y_1(N)_{\overline{\mathbb{F}}_p}$ suffice;
- the description of $F$ on $J_p(\overline{\mathbb{F}}_p)$ as base change by the absolute Frobenius of
  $\overline{\mathbb{F}}_p$, so $F((x) - (x')) = (E^{(p)}, P^{(p)}) - (E'^{(p)}, P'^{(p)})$, and the computation of
  $\langle p \rangle_* F^\vee$ from $F F^\vee = \deg F_{X_1(N)} = p$;
- the computation of $(T_p)_*$ in characteristic $p$ by lifting $(E, P)$ to a henselian discrete valuation ring
  with residue field $\overline{\mathbb{F}}_p$ and fraction field of characteristic $0$ (Néron property and
  separatedness of $J$), the connected–étale sequence $0 \to \mu_p \to \mathcal{E}[p] \to \mathbb{Z}/p\mathbb{Z} \to 0$
  of an ordinary lift, the closures of the $p + 1$ subgroups of order $p$, and the identifications
  $E/\mu_p \cong E^{(p)}$ and $(E/(\mathbb{Z}/p\mathbb{Z}), P \bmod \mathbb{Z}/p\mathbb{Z}) \cong (E^{(p^{-1})}, pP^{(p^{-1})})$ through
  the relative Frobenius and the Verschiebung of $E$;
- the relation $F_{X_1(N)} \circ w_\zeta = w_\zeta \circ I_{p^{-1}} \circ F_{X_1(N)}$, from the compatibility of the
  Weil pairing with base change.

## Sources

- B. Conrad, "The Shimura construction in weight 2", appendix to K. A. Ribet and W. A. Stein,
  *Lectures on Serre's conjectures*, IAS/Park City Mathematics Series; page numbers are those of the
  authors' text at <https://wstein.org/edu/Fall2003/252/references/ribet-stein-serre/ribet-stein.pdf>:
  §5.3, Theorem 5.16 (Eichler–Shimura), p. 70 ("In $\operatorname{End}_{\overline{\mathbf{F}}_p}(J_p)$,
  $(T_p)_* = F + \langle p \rangle_* F^\vee$, $w_\zeta^{-1} F w_\zeta = \langle p \rangle_*^{-1} F$ where $F^\vee$ denotes the
  dual morphism"), with $J_p$, $F$ and $F = \operatorname{Alb}(F_{X_1(N)})$, $F F^\vee = p$ on pp. 69–70; the proof
  of Theorem 5.16, pp. 72–75.
- H. Darmon, F. Diamond and R. Taylor, "Fermat's Last Theorem", page numbers of the authors' text at
  <https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf>: §1.5, pp. 36–37, Theorem 1.29
  ("If $p \nmid N$ then the endomorphism $T_p$ of $J_{\Gamma/\mathbf{F}_p}$ satisfies $T_p = F + \langle p \rangle F'$") and
  Remark 1.30 (Eichler for $\Gamma_0(N)$ and all but finitely many $p$, Shimura for $\Gamma_1(N)$, all $p \nmid N$ by
  the work of Igusa).
- F. Diamond and J. Im, "Modular forms and modular curves", Canadian Mathematical Society Conference
  Proceedings 17 (1995), cited by section and equation numbers: §8.5 ((8.5.1), (8.5.2)) and §10.2, (10.2.3)
  ("$T_{p, \mathbf{F}_p} = \Phi_* + \langle p \rangle_{\mathbf{F}_p, *} \Phi^* = \mathrm{Frob} + \langle p \rangle_{\mathbf{F}_p, *} \mathrm{Ver}$
  in characteristic $p$ if $p$ does not divide $N$").
- P. Deligne, "Formes modulaires et représentations $\ell$-adiques", Séminaire Bourbaki, exp. 355 (1969),
  Lecture Notes in Math. 179, Springer (1971), 139–172, <http://www.numdam.org/item?id=SB_1968-1969__11__139_0>:
  Théorème 4.9 (Formule de congruence), p. 167, the form "$T_p = F + I_p^* V$, $FV = p^{k+1}$" of the relation on the
  $\ell$-adic cohomology ${}_nW_\ell$ of the curves of full level $n$ (his $k$ is the weight minus $2$), with "Le
  théorème suivant, synonyme de (4.8), remonte à Eichler".
- F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228, Springer
  (2005): §8.7, "The Eichler–Shimura Relation", p. 349, from the table of contents; the section itself was not read.
