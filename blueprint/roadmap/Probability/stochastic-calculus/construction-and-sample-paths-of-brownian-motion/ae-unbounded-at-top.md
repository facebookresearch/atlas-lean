# Brownian motion is unbounded above and below at infinity

Let $B$ be a real Brownian motion. Then almost surely, for every level $A \in \mathbb{R}$ and every $N \in \mathbb{N}$,
there are integer times $n, m \ge N$ with $B_n > A$ and $B_m < A$; in particular
$\limsup_{t \to \infty} B_t = +\infty$ and $\liminf_{t \to \infty} B_t = -\infty$.

One proof avoids scaling: it applies the
[random-walk dichotomy](../../random-walks/drift-and-oscillation-of-random-walks/random-walk-dichotomy-zero.md)
to the walk $(B_n)$ with i.i.d. $N(0, 1)$ steps and rules out the zero walk and the two drifts,
since $P(B_n > 0) = P(B_n < 0) = 1/2$.

## Informally uses

- [Brownian motion oscillates immediately after time zero](../blumenthal-zero-one-law/ae-exists-pos-and-neg.md):
  Le Gall's proof starts from $P(\sup_{s \le 1} B_s > 0) = 1$ and uses Brownian scaling to get
  $P(\sup_s B_s > A) = 1$ for every $A$.

## Sources

- J.-F. Le Gall, *Intégration, Probabilités et Processus Aléatoires*, lecture notes, École normale supérieure, Corollaire 14.4.3 (third assertion).
