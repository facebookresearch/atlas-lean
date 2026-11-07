# Entropy of a map relative to a partition

Let $\mu$ be a measure on a measurable space
$M$, let $T : M \to M$ be a map and let $P$ be a finite family of subsets of $M$. The entropy of
$T$ relative to $P$ is

$$h_\mu(T, P) = \limsup_{n \to \infty} \frac{1}{n} H_\mu\Big(\bigvee_{k=0}^{n-1} T^{-k} P\Big),$$

where $\bigvee_{k=0}^{n-1} T^{-k} P$ is the iterated join of $P$ under $T$; the Shannon entropy
of a finite family $Q$ of sets is $H_\mu(Q) = \sum_{A \in Q} -\mu(A) \log \mu(A)$, with
$0 \log 0 = 0$ and with $\mu(A)$ replaced by $0$ when $\mu(A) = \infty$; and the limit superior
is taken to be $0$ when it is $+\infty$ or $-\infty$.
