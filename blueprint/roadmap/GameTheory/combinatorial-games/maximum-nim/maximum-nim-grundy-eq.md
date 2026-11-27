# Recursive formula for Maximum Nim Grundy numbers

For every rule function
$f : \mathbb{N} \to \mathbb{N}$ and every pile size $x \in \mathbb{N}$, the Grundy number $G_f(x)$
of a pile of $x$ stones in Maximum Nim with rule function $f$ equals the mex (least natural number
not in the set) of $\{G_f(x - u) : 1 \le u \le \min(f(x), x)\}$.

## Sources

- Shoei Takahashi, Hikaru Manabe, Ryohei Miyadera, *Maximum Nim and the Josephus Problem*, INTEGERS 24 (2024), Article G5, Section 2.
