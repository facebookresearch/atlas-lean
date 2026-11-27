# Minimum ranks under five-wise independence

Let $h : \iota \times X \to \{0, \dots, q-1\}$ be five-wise independent with uniform seed, $S \subseteq X$ finite with $0 < |S| \le q$, and $x \notin S$. Then

$$
\Pr_i\bigl[h_i(x) \le h_i(y) \text{ for all } y \in S\bigr] \le \frac{256}{|S|},
$$

ties counting toward the event. Consequently, for any family $(w_a)_{a \in \mathcal{A}}$ of windows $w_a = (w_a(0), \dots, w_a(L))$ of $L + 1$ points ($0 < L \le q$), some seed makes an endpoint of the window a weak minimum of the window for at most $512\,|\mathcal{A}|/L$ of the injective windows.

## Proof sketch

Conditioned on the rank of $x$, the indicators that competitors have smaller rank are four-wise independent with mean $\rho$; a fourth-moment bound shows that none is smaller with probability $O(1/(|S|\rho)^2)$ when $|S|\rho \ge 1$. Summing over the rank of $x$ and telescoping consecutive reciprocals gives the inverse-linear bound; averaging over seeds gives the window statement.

## Depends on

- [k-wise independent hash families](../../../data-structures/hashing/succinct-dictionaries-and-hash-families/word-ram-hash-families/k-wise-independent-hash-family.md)

## Sources

- M. B. T. Knudsen and M. Stöckel, "Quicksort, Largest Bucket, and Min-Wise Hashing with Limited Independence", European Symposium on Algorithms (ESA 2015), 2015.
