# Leftover hashing from concentrated conditional entropy

Let $(h_s)$ be a hash family into a finite set $\mathrm{Out}$ with $\Pr_s[h_s(x) = h_s(y)] \le 1/|\mathrm{Out}|$ for $x \ne y$.

1. (Smoothing) For a source $p$ and $m \ge 0$, the statistical distance between $(s, h_s(x))$ with $x \sim p$ and $(s, u)$ with $u$ uniform is at most $2\Pr_p[p(x) > m] + \frac12\sqrt{2m|\mathrm{Out}|}$; with public side information only the average probability of heavy conditional outcomes is charged.
2. (Independent conditional sources) Let $(Y_i, X_i)_{i \in I}$ be independent pairs with positive masses at least $2^{-B}$, and hash the whole tuple $X = (X_i)$. Then for every $\varepsilon \ge 0$ the joint law of $((Y_i)_i, s, h_s(X))$ is within statistical distance

$$
2\exp\Big(-\frac{2\varepsilon^2}{|I|B^2}\Big) + \frac12\sqrt{2\,|\mathrm{Out}|\, 2^{-(\sum_i H(X_i\mid Y_i) - \varepsilon)}}
$$

of $((Y_i)_i, s, u)$ with $u$ uniform and independent.

## Proof sketch

Discard the heavy outcomes: conditioning the source on light outcomes changes it by at most the heavy probability on each side and leaves masses at most $2m$ after renormalization (when the heavy probability is at most $1/2$; otherwise the bound is trivial), so the leftover hash lemma applies. For item 2, concentration of conditional information shows the heavy event has probability at most $e^{-2\varepsilon^2/(|I|B^2)}$ at threshold $2^{-(\sum_i H - \varepsilon)}$, and the side-information form of item 1 combines the two errors.

## Depends on

- [Leftover hash lemma with side information](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma-with-side-information.md)
- [Universal hash family](../../../ComputerScience/data-structures/hashing/universal-hashing/is-universal.md)

## Proof depends on

- [Leftover hash lemma with side information](../../../ComputerScience/cryptography/randomness-extraction/leftover-hash-lemma-with-side-information.md)
- [Concentration of conditional information in independent samples](concentration-of-conditional-information.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography Conference (TCC), 2006.
- S. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1-3), 2012.
