# Type classes outside the support have probability zero

Let $\alpha$ be a finite alphabet. An $n$-type is a multiset $s$ of $n$ letters, with letter counts $k_a(s)$; the type of a sequence $x \in \alpha^n$ is the multiset of its letters, $T_s$ is the set of sequences of type $s$, and $P_s(a) = k_a(s)/n$ is the empirical distribution. For $Q : \alpha \to \mathbb{R}$ and a set $S \subseteq \alpha^n$, $Q^n(S) = \sum_{x \in S} \prod_{i<n} Q(x_i)$.
If some letter $a$ has $k_a(s) > 0$ but $Q(a) = 0$, then $Q^n(T_s) = 0$; this is the case $D(P \| Q) = \infty$
of (II.5) in Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998).
