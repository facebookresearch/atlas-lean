# Probability of a type class under its own type

Let $\alpha$ be a finite alphabet. An $n$-type is a multiset $s$ of $n$ letters, with letter counts $k_a(s)$; the type of a sequence $x \in \alpha^n$ is the multiset of its letters, $T_s$ is the set of sequences of type $s$, and $P_s(a) = k_a(s)/n$ is the empirical distribution. For $Q : \alpha \to \mathbb{R}$ and a set $S \subseteq \alpha^n$, $Q^n(S) = \sum_{x \in S} \prod_{i<n} Q(x_i)$.
For $n \ge 1$ and an $n$-type $s$ with empirical distribution $P = P_s$,
$P^n(T_s) = |T_s|\, e^{-nH(P)}$ with $H(P) = \sum_a -P(a)\log P(a)$ (natural logarithm, $0 \log 0 = 0$) (Csiszár,
"The method of types", IEEE Trans. Inform. Theory 44 (1998), proof of Lemma II.2).
