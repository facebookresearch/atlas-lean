# Mean-field coordinate-ascent sweep

Let $A$ and $B$ be finite sets and
$p : A \times B \to \mathbb{R}$. One sweep of coordinate ascent (CAVI) sends a pair of factors
$(q_1, q_2)$, with $q_1 : A \to \mathbb{R}$ and $q_2 : B \to \mathbb{R}$, to $(q_1', q_2')$, where
$q_1'$ is the CAVI update of the first factor given $q_2$,
$q_1'(a) = \exp(\sum_b q_2(b) \log p(a, b)) / \sum_{a'} \exp(\sum_b q_2(b) \log p(a', b))$, and
$q_2'$ is the CAVI update of the second factor given the new first factor $q_1'$,
$q_2'(b) = \exp(\sum_a q_1'(a) \log p(a, b)) / \sum_{b'} \exp(\sum_a q_1'(a) \log p(a, b'))$.
The old first factor $q_1$ is not used.

Here $\log x$ means $\log |x|$ for $x \ne 0$ and $\log 0 = 0$, so $p$ need not be positive.
