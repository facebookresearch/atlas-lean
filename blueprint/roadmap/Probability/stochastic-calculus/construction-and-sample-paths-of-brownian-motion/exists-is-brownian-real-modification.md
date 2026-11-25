# Brownian motion as a continuous modification of pre-Brownian motion

Let $B$ be a pre-Brownian motion (a real process with the finite-dimensional laws of Brownian motion) with
measurable coordinates on a probability space. Then $B$ has a modification $W$ ($W_t = B_t$ almost surely,
for each $t$) with measurable coordinates and continuous paths (on every sample), and $W$ is a Brownian
motion. The continuity comes from Kolmogorov's lemma applied to the fourth moments of the increments; Le
Gall's ENS notes obtain continuity differently, in the proof of Théorème 14.2.1, from the uniform
convergence of the Haar–Schauder (Lévy–Ciesielski) series.

## Informally uses

- [Kolmogorov continuous-modification theorem for real-valued processes](../kolmogorov-continuity-theorem/exists-continuous-modification.md):
  Kolmogorov's lemma produces the continuous modification.
- [Kolmogorov's condition for pre-Brownian motion](is-kolmogorov-process.md): the moment bound
  $\mathbb E |B_s - B_t|^4 \le 3 |s - t|^2$ that Kolmogorov's lemma needs, with $p = 4$ and $q = 2 > 1$.

## Sources

- J.-F. Le Gall, DEA lecture notes, 1994, Lemme 2.3.
- J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires*, lecture notes, École normale supérieure, Théorème 14.2.1.
