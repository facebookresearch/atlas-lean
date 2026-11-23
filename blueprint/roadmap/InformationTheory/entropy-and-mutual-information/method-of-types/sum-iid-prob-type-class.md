# The type classes partition the sequences

Let $\alpha$ be a finite alphabet. An $n$-type is a multiset $s$ of $n$ letters, with letter counts $k_a(s)$; the type of a sequence $x \in \alpha^n$ is the multiset of its letters, $T_s$ is the set of sequences of type $s$, and $P_s(a) = k_a(s)/n$ is the empirical distribution. For $Q : \alpha \to \mathbb{R}$ and a set $S \subseteq \alpha^n$, $Q^n(S) = \sum_{x \in S} \prod_{i<n} Q(x_i)$.
Summing $Q^n(T_s)$ over all $n$-types $s$ gives $Q^n(\alpha^n)$ (Csiszár, "The method of types", IEEE Trans.
Inform. Theory 44 (1998), proof of Lemma II.2).
