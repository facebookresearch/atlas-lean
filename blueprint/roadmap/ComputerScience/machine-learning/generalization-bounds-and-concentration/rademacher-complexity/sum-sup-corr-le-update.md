# One step of the contraction argument

Let $A \subseteq \mathbb{R}^n$ be nonempty and bounded, let every $g_i$ be $L$-Lipschitz with $L \ge 0$, and let $g'$ agree with $g$ except that $g'_j(x) = L x$. Then the sum over sign vectors of $\sup_{a \in A} \sum_i \sigma_i g_i(a_i)$ is at most the same sum for $g'$. Pairing $\sigma$ with the sign vector reversed at $j$, for $a, a' \in A$ one has $g_j(a_j) - g_j(a'_j) \le L \lvert a_j - a'_j \rvert$, and the right side is $L a_j - L a'_j$ or $L a'_j - L a_j$, which is attained by the pair $(a, a')$ or $(a', a)$ for $g'$.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), proof of Lemma 26.9.
