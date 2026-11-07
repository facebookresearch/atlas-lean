# Grundy number where the rule function is flat

Let $f : \mathbb{N} \to \mathbb{N}$
satisfy $f(0) = 0$ and $f(m-1) \le f(m) \le f(m-1) + 1$ for every $m \ge 1$, and let $G$ be the
Grundy number of Maximum Nim with rule function $f$. If $x \ge 1$ and $f(x) = f(x-1)$, then
$G(x) = G(x - f(x) - 1)$.

Here $x - f(x) - 1 \ge 0$, since the hypotheses give $f(x) = f(x-1) \le x - 1$.

## Sources

- Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*, INTEGERS 24 (2024), Article G5, Lemma 1(ii) (`integers-2024-G5-lem-1`).
