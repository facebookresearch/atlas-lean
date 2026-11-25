# Expander mixing lemma for matrices

Let $A$ be a symmetric real matrix indexed by a finite set $V$ of size $N$, and let $d$ and $c \ge 0$ be real numbers such that every row of $A$ sums to $d$ ($A \mathbf 1 = d \mathbf 1$) and $\lVert A x\rVert \le c \lVert x\rVert$ for every $x$ whose entries sum to $0$. Then for all $S, T \subseteq V$, with quotients by $N = 0$ read as $0$,

$$\Big\lvert 1_S^{\mathsf T} A\, 1_T - \frac{d\, \lvert S\rvert\, \lvert T\rvert}{N} \Big\rvert \le c \sqrt{\lvert S\rvert \Big(1 - \frac{\lvert S\rvert}{N}\Big)} \sqrt{\lvert T\rvert \Big(1 - \frac{\lvert T\rvert}{N}\Big)}.$$

This is the proof of the expander mixing lemma in S. Vadhan, *Pseudorandomness* (2012), Lemma 4.15, which uses only these three properties of the adjacency matrix.
