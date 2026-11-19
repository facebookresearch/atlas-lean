# Counting sample pairs by overlap with a given pair

Let $n$ be a natural number, $s$ a [pair of genes](sample-pairs.md) of a sample of size $n$ and $f$ a real function on the natural numbers. Then

$$\sum_{t} f(|s \cap t|) = f(2) + 2(n-2)\, f(1) + \binom{n-2}{2} f(0),$$

the sum running over the pairs $t$ of the sample: one pair equals $s$, $2(n-2)$ share exactly one gene with it and $\binom{n-2}{2}$ are disjoint from it.
