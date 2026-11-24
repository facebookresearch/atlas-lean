# Lower bound on the size of a type class, polynomial form

Let $\alpha$ be a finite alphabet. An $n$-type is a multiset $s$ of $n$ letters, with letter counts $k_a(s)$; the type of a sequence $x \in \alpha^n$ is the multiset of its letters, $T_s$ is the set of sequences of type $s$, and $P_s(a) = k_a(s)/n$ is the empirical distribution.
For $n \ge 1$ and an $n$-type with empirical distribution $P$, with the natural logarithm,
$e^{nH(P)} \le (n + 1)^{|\alpha|}\, |T_P|$, that is $(n + 1)^{-|\alpha|} e^{nH(P)} \le |T_P|$ (Csiszár, "The
method of types", IEEE Trans. Inform. Theory 44 (1998), (II.4) combined with Lemma II.1).
