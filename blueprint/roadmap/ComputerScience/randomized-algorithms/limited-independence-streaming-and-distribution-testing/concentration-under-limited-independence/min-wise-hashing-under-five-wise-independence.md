# Minimum ranks under five-wise independence

Let $h : \iota \times X \to \{0, \dots, q-1\}$ be five-wise independent with uniform seed, $S \subseteq X$ finite with $0 < |S| \le q$, and $x \notin S$. Then

$$
\Pr_i\bigl[h_i(x) \le h_i(y) \text{ for all } y \in S\bigr] \le \frac{256}{|S|},
$$

ties counting toward the event. Consequently, for any family $(w_a)_{a \in \mathcal{A}}$ of windows $w_a = (w_a(0), \dots, w_a(L))$ of $L + 1$ points ($0 < L \le q$), some seed makes an endpoint of the window a weak minimum of the window for at most $512\,|\mathcal{A}|/L$ of the injective windows.

## Proof sketch

Condition on $h_i(x) = \alpha$ and let $\rho = \alpha/q$. The indicators $[h_i(y) < \alpha]$, $y \in S$, are four-wise independent with mean $\rho$, so the fourth central moment of their sum $Z$ is at most $|S|\rho + 3(|S|\rho)^2$ and $\Pr[Z = 0] \le 4/(|S|\rho)^2$ when $|S|\rho \ge 1$. Averaging over $\alpha$, the values $\alpha < 2q/|S|$ contribute at most $2/|S| + 1/q$ and the others at most $4/|S|$, so the probability is at most $7/|S|$ since $|S| \le q$. For the windows, apply the bound to each endpoint against the other $L$ points of an injective window and average over seeds.

## Depends on

- [k-wise independent hash family](../../../data-structures/hashing/succinct-dictionaries-and-hash-families/word-ram-hash-families/k-wise-independent-hash-family.md)

## Sources

- M. B. T. Knudsen and M. Stöckel, "Quicksort, Largest Bucket, and Min-Wise Hashing with Limited Independence", European Symposium on Algorithms (ESA 2015), LNCS 9294, 2015, Theorem 2: the bound $O(1/(|S|+1))$ for hash values in $(0,1)$ with strict inequality. The explicit constant for the discrete range with ties follows from the same fourth-moment argument (it gives $7/|S|$).
