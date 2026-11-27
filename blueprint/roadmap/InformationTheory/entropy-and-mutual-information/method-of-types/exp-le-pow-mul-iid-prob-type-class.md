# Lower bound on the probability of a type class, polynomial form

Let $\alpha$ be a finite alphabet. An $n$-type is a multiset $s$ of $n$ letters, with letter counts $k_a(s)$; the type of a sequence $x \in \alpha^n$ is the multiset of its letters, $T_s$ is the set of sequences of type $s$, and $P_s(a) = k_a(s)/n$ is the empirical distribution. For $Q : \alpha \to \mathbb{R}$ and a set $S \subseteq \alpha^n$, $Q^n(S) = \sum_{x \in S} \prod_{i<n} Q(x_i)$.
For $n \ge 1$, an $n$-type with empirical distribution $P$, and $Q \ge 0$ with $Q(a) > 0$ wherever $P(a) > 0$,
$e^{-nD(P \| Q)} \le (n + 1)^{|\alpha|}\, Q^n(T_P)$, with $D(P \| Q) = \sum_a P(a)\log(P(a)/Q(a))$ (Csiszár, "The
method of types", IEEE Trans. Inform. Theory 44 (1998), (II.5) combined with Lemma II.1).
