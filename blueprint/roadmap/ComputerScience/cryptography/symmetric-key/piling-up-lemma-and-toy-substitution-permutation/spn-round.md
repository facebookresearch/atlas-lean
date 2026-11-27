# Spn Round

Let $m \in \mathbb{N}$ be a width, $k \in \mathrm{Bool}^m$ a round key, $S : \mathrm{Bool}^m \to \mathrm{Bool}^m$ an **arbitrary** map (no invertibility or other structure is assumed) and $\pi$ a permutation of $\{0, \dots, m-1\}$. One round maps a state $x \in \mathrm{Bool}^m$ to the word whose $i$th bit is

$$
\mathrm{spnRound}(k, S, \pi, x)_i = S(x \oplus k)_{\pi(i)},
$$

where $x \oplus k$ is the [coordinatewise XOR](../../hash-functions/hmac/xor-block.md) of $x$ and $k$: the key is added by XOR (not integer addition), the substitution is applied to the whole word, and the result is [permuted](permute.md) by $\pi$.
