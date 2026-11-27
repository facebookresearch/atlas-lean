# Rankin–Selberg series of a primitive form

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ and $k \ge 1$ an integer with
$\varepsilon(-1) = (-1)^k$, and let $f = \sum_{n \ge 1} a_n q^n$, $q = e^{2\pi i z}$, be a primitive cusp form (newform) of
type $(k, \varepsilon)$ on $\Gamma_0(N)$, normalized by $a_1 = 1$. Then the Dirichlet series
$\sum_{n \ge 1} |a_n|^2 n^{-s}$ converges for $\operatorname{Re}(s) > k$, and its product

$$\zeta(2s - 2k + 2) \sum_{n \ge 1} |a_n|^2 n^{-s}$$

with the Riemann zeta function extends to a meromorphic function on the whole complex plane that is holomorphic on the
half-plane $\operatorname{Re}(s) > k - 1$ except for a simple pole at $s = k$.

Deligne and Serre quote this from Rankin for the proof of
[Rankin's bound](rankin-bound-for-the-mean-square-of-hecke-eigenvalues.md), which uses it only on
$\operatorname{Re}(s) \ge k$. The statement here is weaker than their wording, which names $s = k$ as the only pole in the
whole plane: that holds for $N = 1$, but for $N > 1$ the Euler factors of $\zeta(2s - 2k + 2)$ at the primes dividing $N$
can give poles on the line $\operatorname{Re}(s) = k - 1$. That the pole at $s = k$ is simple is how they use it, since they
conclude from it that the series $L(s)$ of that page has a simple pole at $s = k$.

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the definition of primitive forms of type $(k, \varepsilon)$ on $\Gamma_0(N)$ (Deligne–Serre, §1.7, citing Atkin–Lehner
  for $\varepsilon = 1$ and Deligne, Li and Miyake in general, as cited there);
- a proof of the convergence and of the continuation with its only pole, which Deligne–Serre attribute to Rankin [18],
  also citing Li [12], Miyake [13] and Ogg [15] (as cited in Deligne–Serre (1974), p. 518).

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): Démonstration 5.2, pp. 518–519 ("D'après [18] (cf. aussi
  [12], [13] et [15]), la série $\sum |a_n|^2 n^{-s}$ converge pour $\mathscr{R}(s) > k$ et son produit par
  $\zeta(2s-2k+2)$ se prolonge en une fonction méromorphe dans tout le plan complexe, avec pour unique pôle le point
  $s = k$"), with the simple pole of $L(s)$ at $s = k$ on p. 519; §1.7, p. 509, for primitive forms.
- R. A. Rankin, *Contributions to the theory of Ramanujan's function τ(n) and similar arithmetical functions. I, II*,
  Proc. Cambridge Philos. Soc. 35 (1939), 351–372, as cited in Deligne–Serre (1974), p. 518; not read.
- W. Li, *Newforms and functional equations* (Math. Ann., to appear, as cited); T. Miyake, *On automorphic forms on
  GL₂ and Hecke operators*, Ann. of Math. 94 (1971), 174–189; A. P. Ogg, *On a convolution of L-series*, Invent. Math. 7
  (1969), 297–312: each as cited in Deligne–Serre (1974), p. 518; not read.
