# Galois representations attached to newforms and their Hodge filtration at p

This node is still to be broken down. Let $f = \sum_{n \ge 1} a_n q^n$ be a
[newform](../../modular-forms-q-series/modular-forms/hecke-eigenforms-and-newforms-for-gamma1-n.md) of weight
$k \ge 2$ and level $N$, with nebentypus $\varepsilon$, extended to $\mathbb{Z}$ by $\varepsilon(\ell) = 0$ for
$\ell \mid N$. Let $F = \mathbb{Q}(a_n : n \ge 1) \subset \mathbb{C}$, a number field, let $p$ be a prime, $\lambda$ a
finite place of $F$ above $p$ and $F_\lambda$ the completion of $F$ at $\lambda$. Fix, for each prime $\ell$, an
embedding $\overline{\mathbb{Q}} \to \overline{\mathbb{Q}}_\ell$, which makes $G_{\mathbb{Q}_\ell}$ a decomposition
group at $\ell$ in $G_{\mathbb{Q}} = \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, with inertia subgroup
$I_\ell$, and let $\mathrm{Fr}_\ell \in G_{\mathbb{Q}_\ell}$ be an arithmetic Frobenius element. Let $\kappa$ be the
$p$-adic cyclotomic character, and view $\varepsilon$ as a character of $G_{\mathbb{Q}}$ through
$G_{\mathbb{Q}} \to \operatorname{Gal}(\mathbb{Q}(\zeta_N)/\mathbb{Q}) \cong (\mathbb{Z}/N\mathbb{Z})^\times$.

Then there is a two-dimensional $F_\lambda$-vector space $V = V_{F_\lambda}(f)$ with a continuous
$F_\lambda$-linear action of $G_{\mathbb{Q}}$ such that:

1. for every prime $\ell \ne p$,
   $\det_{F_\lambda}(1 - \mathrm{Fr}_\ell^{-1} u \,;\, V^{I_\ell}) = 1 - a_\ell u + \varepsilon(\ell) \ell^{k-1} u^2$;
   in particular, for $\ell \nmid Np$, $V$ is unramified at $\ell$ and the geometric Frobenius
   $\mathrm{Fr}_\ell^{-1}$ acts on $V$ with trace $a_\ell$ and determinant $\varepsilon(\ell) \ell^{k-1}$;
2. $G_{\mathbb{Q}}$ acts on $\det_{F_\lambda} V$ through $\kappa^{1-k} \varepsilon^{-1}$;
3. $V$, restricted to $G_{\mathbb{Q}_p}$, is a de Rham representation, and the filtration of the two-dimensional
   $F_\lambda$-vector space $D_{\mathrm{dR}}(V) = (B_{\mathrm{dR}} \otimes_{\mathbb{Q}_p} V)^{G_{\mathbb{Q}_p}}$
   satisfies $\operatorname{Fil}^i D_{\mathrm{dR}}(V) = D_{\mathrm{dR}}(V)$ for $i \le 0$,
   $\operatorname{Fil}^i D_{\mathrm{dR}}(V) = 0$ for $i \ge k$, and $\operatorname{Fil}^i D_{\mathrm{dR}}(V)$ is
   one-dimensional over $F_\lambda$ for $1 \le i \le k - 1$.

So the jumps of the Hodge filtration are $0$ and $k - 1$, each once over $F_\lambda$: for every embedding of
$F_\lambda$ into $\overline{\mathbb{Q}}_p$, the Hodge–Tate weights of $V$ are $\{0, k - 1\}$ in the convention in
which the cyclotomic character has weight $-1$.

Kato constructs $V_{F_\lambda}(f)$ as the largest quotient of
$H^1_{\mathrm{et}}(Y_1(N) \otimes \overline{\mathbb{Q}}, \operatorname{Sym}^{k-2}(\mathcal{H}^1_p)) \otimes_{\mathbb{Q}_p} F_\lambda$,
for the first relative $p$-adic cohomology $\mathcal{H}^1_p$ of the universal elliptic curve, on which each Hecke
operator $T(n)$ acts as $a_n$ (with an ad hoc definition of the cohomology for $N \le 3$). Items 1 and 2 are the results he reviews as known
in §14.10, with references to Carayol and Saito; item 3 is his (9.2.2) for the newform, from the comparison
theorems of Faltings and Tsuji.

A good expansion has pages for: the étale cohomology of the modular curves $Y_1(N)$ with coefficients in
$\operatorname{Sym}^{k-2}$ of the universal elliptic curve, with its Hecke action, and the quotient
$V_{F_\lambda}(f)$; the Eichler–Shimura congruence relation, which gives item 1 for $\ell \nmid Np$; the
local–global compatibility at the primes $\ell \mid N$, $\ell \ne p$ (Carayol, Saito); the determinant, from
Poincaré duality; and the de Rham comparison theorem for the Kuga–Sato varieties, with the identification of
the Hodge filtration with the modular forms $M_k(X_1(N))$ that gives item 3.

## Depends on

- [Hecke eigenforms and newforms for Γ₁(N)](../../modular-forms-q-series/modular-forms/hecke-eigenforms-and-newforms-for-gamma1-n.md), for newforms, their nebentypus and their coefficient field
- [de Rham representations](p-adic-hodge-theory/de-rham-representations.md), for $D_{\mathrm{dR}}$, its filtration and the sign convention of the weights
- [Hodge–Tate representations](p-adic-hodge-theory/hodge-tate-representations.md), for the Hodge–Tate weights
- [Cyclotomic character and Tate twists](cyclotomic-character-and-tate-twists.md), for $\kappa$
- [Inertia and tame inertia of a p-adic field](weil-deligne-representations/inertia-and-tame-inertia-of-a-p-adic-field.md), for the inertia groups $I_\ell$ and the Frobenius elements

## Proof depends on

Its proof uses the inputs listed in the expansion note.

## Sources

- K. Kato, "p-adic Hodge theory and values of zeta functions of modular forms", Astérisque 295 (2004),
  117–290, <https://www.numdam.org/item/AST_2004__295__117_0.pdf>: §6.3, pp. 161–162 ($F = \mathbb{Q}(a_n ; n \ge 1)$,
  a finite extension of $\mathbb{Q}$, and $V_F(f)$, "the quotient of $V_{k,F}(Y_1(N))$ by the $F$-submodule generated
  by the images of $T(n) \otimes 1 - 1 \otimes a_n$ for all $n \geq 1$", a quotient of $V_{k,\mathbb{Q}}(Y_1(N))$ as a
  $\mathbb{Q}$-vector space, of dimension $2$ over $F$; $V_A(f) = V_F(f) \otimes_F A$); §8.3, pp. 181–182
  ($F_\lambda$, the action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $V_{F_\lambda}(f)$, unramified at
  the primes not dividing $pMN$ on the cohomology of $Y(M, N)$, and the ad hoc definition for $N \le 3$); (9.2.2),
  p. 187 ($V_{k,\mathbb{Q}_p}(Y)$ is de Rham, $D_{\mathrm{dR}}^i = D_{\mathrm{dR}}$ for $i \le 0$, $0$ for $i \ge k$,
  and $M_k(X) \otimes \mathbb{Q}_p$ for $1 \le i \le k - 1$, citing Faltings and Tsuji); §9.4, p. 188 ("Let $f$ be
  a normalized newform in $M_k(X_1(N)) \otimes \mathbb{C}$ of weight $k$ and of level $N$ … Then by (9.2.2),
  $V_{F_\lambda}(f)$ is a de Rham representation of $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$,
  $D_{\mathrm{dR}}^i(V_{F_\lambda}(f)) = D_{\mathrm{dR}}(V_{F_\lambda}(f))$ for $i \le 0$,
  $D_{\mathrm{dR}}^i(V_{F_\lambda}(f)) = 0$ for $i \ge k$, … $D_{\mathrm{dR}}^i(V_{F_\lambda}(f)) = S(f) \otimes_F F_\lambda$
  for $1 \le i \le k - 1$", with $S(f)$ one-dimensional over $F$ by §6.3); §14.10, pp. 240–241, (14.10.2)
  ("The action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $\det_{F_\lambda}(V_{F_\lambda}(f))$ is given by
  $\kappa^{1-k}\varepsilon^{-1}$") and (14.10.3) ("For any prime number $\ell$ which is not divided by $\lambda$,
  $\det_{F_\lambda}(1 - \mathrm{Fr}_\ell^{-1} u ; H^0(\mathbb{Q}_\ell^{\mathrm{ur}}, V_{F_\lambda}(f))) = 1 - a_\ell u +
  \varepsilon(\ell)\ell^{k-1}u^2$. Here $\mathrm{Fr}_\ell$ is the arithmetic Frobenius of $\ell$"), stated there as
  known, with references to Carayol and Saito.
