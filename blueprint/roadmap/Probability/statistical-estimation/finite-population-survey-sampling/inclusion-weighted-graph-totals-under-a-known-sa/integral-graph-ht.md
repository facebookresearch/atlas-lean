# Unbiasedness of the Horvitz-Thompson graph-total estimator

Let $V$ be a finite vertex set, $p$ a sampling design (a probability distribution on subsets $s \subseteq V$), $k \in \mathbb N$, and $y$ a real value on $k$-subsets of $V$. A $k$-subset $M$ is observed when $M \subseteq s$; let $\pi(M) = P(M \subseteq s)$. If $\pi(M) > 0$ for every $k$-subset $M$, then the Horvitz-Thompson estimator $\sum_{M \text{ observed}} y(M)/\pi(M)$ has expectation equal to the graph total $\sum_{|M| = k} y(M)$. This covers vertex totals ($k = 1$), dyads and edges ($k = 2$) and motifs ($k = 3$).
