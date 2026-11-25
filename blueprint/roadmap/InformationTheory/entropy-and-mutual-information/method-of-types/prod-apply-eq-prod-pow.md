# The probability of a sequence depends only on its type

Let $\alpha$ be a finite alphabet. An $n$-type is a multiset $s$ of $n$ letters, with letter counts $k_a(s)$; the type of a sequence $x \in \alpha^n$ is the multiset of its letters, $T_s$ is the set of sequences of type $s$, and $P_s(a) = k_a(s)/n$ is the empirical distribution.
For $Q : \alpha \to \mathbb{R}$ and $x \in \alpha^n$, $\prod_{i<n} Q(x_i) = \prod_{a} Q(a)^{n_a}$, where $n_a$ is the
number of occurrences of $a$ in $x$ (Csiszár, "The method of types", IEEE Trans. Inform. Theory 44 (1998), first
line of (II.1)).
