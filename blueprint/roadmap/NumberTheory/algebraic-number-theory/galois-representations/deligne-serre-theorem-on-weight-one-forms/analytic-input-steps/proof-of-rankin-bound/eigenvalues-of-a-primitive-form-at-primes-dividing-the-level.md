# Absolute values of the eigenvalues of a primitive form at the primes dividing the level

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ and $k \ge 1$ an integer with $\varepsilon(-1) = (-1)^k$, let
$f = \sum_{n \ge 1} a_n q^n$ be a [primitive form](primitive-forms-of-type-k-epsilon.md) of type $(k, \varepsilon)$ on
$\Gamma_0(N)$, and let $p$ be a prime dividing $N$. Then:

1. $a_p = 0$ if $p^2 \mid N$ and $\varepsilon$ is defined modulo $N/p$;
2. $|a_p| = p^{(k-1)/2}$ if $\varepsilon$ is not defined modulo $N/p$;
3. $|a_p| = p^{k/2 - 1}$ if $p^2 \nmid N$ and $\varepsilon$ is defined modulo $N/p$.

In particular $|a_p| < p^{k/2}$.

Here $N$ is the level of the primitive form $f$ itself.
[Rankin's bound](rankin-bound-for-the-mean-square-of-hecke-eigenvalues.md) applies this to the primitive form $f_0$ of a
level $M$ that divides the level of the eigenform it starts from, so that there these formulas hold at level $M$, with
the primes dividing $M$ in the place of those dividing $N$.

This is the rule of §1.8 of Deligne–Serre, who cite Li and Ogg for it and note that the third case does not occur for
$k = 1$. It is Theorem 3 (ii)–(iii) of Li, whose third case is the more precise $a_p^2 = \varepsilon(p) p^{k-2}$, with
$\varepsilon(p)$ the value at $p$ of $\varepsilon$ as a character modulo $N/p$.

## Depends on

- [Primitive forms of type (k, ε) on Γ₀(N)](primitive-forms-of-type-k-epsilon.md)

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

This node is still to be broken down. A good expansion states and links:

- for $\varepsilon$ defined modulo $N/p$ and $p^2 \mid N$: $U_p$ maps $S_k(N, \varepsilon)$ into $S_k(N/p, \varepsilon)$ (Li, Lemma 1,
  p. 287), so $a_p f = f|U_p$ is an old form, and $a_p = 0$ as $f$ is new (Li, p. 295, Case I i);
- for $\varepsilon$ defined modulo $N/p$ and $p^2 \nmid N$: Li's operator $V_p^N$ and her Lemmas 2 and 3 (pp. 288–289), which
  give $f|U_p = -p^{k/2-1} f|V_p^N$ and, with $f|V_p^N|V_p^N = \varepsilon(p) f$, the relation $a_p^2 = \varepsilon(p) p^{k-2}$
  (Li, p. 295, Case I ii);
- for $\varepsilon$ not defined modulo $N/p$: Corollary 1 of Ogg's *On the eigenvalues of Hecke operators*, as Li applies it
  (p. 295, Case II).

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §1.8, pp. 509–510.
- W.-C. W. Li, *Newforms and functional equations*, Math. Ann. 212 (1975), 285–315: Lemma 1, p. 287; Lemma 2, p. 288;
  Lemma 3, p. 289; Theorem 3 (ii)–(iii) and its proof, p. 295.
- A. P. Ogg, *On the eigenvalues of Hecke operators*, Math. Ann. 179 (1969), 101–108: Corollary 1, as cited in Li (1975),
  p. 295; not read.
