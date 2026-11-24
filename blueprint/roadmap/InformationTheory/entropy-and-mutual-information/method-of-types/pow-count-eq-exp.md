# One letter of the sequence-probability formula

Let $\alpha$ be a finite alphabet. An $n$-type is a multiset $s$ of $n$ letters, with letter counts $k_a(s)$; the type of a sequence $x \in \alpha^n$ is the multiset of its letters, $T_s$ is the set of sequences of type $s$, and $P_s(a) = k_a(s)/n$ is the empirical distribution.
Let $n \ge 1$, let $s$ be an $n$-type, $a$ a letter with count $k = k_a(s)$ and $P(a) = k/n$, and let
$Q : \alpha \to \mathbb{R}$ with $Q(a) > 0$ if $k > 0$. Then, with the natural logarithm and $0 \log 0 = 0$,
$Q(a)^k = \exp\bigl(-n\,(-P(a)\log P(a) + P(a)\log(P(a)/Q(a)))\bigr)$ (Csiszár, "The method of types", IEEE
Trans. Inform. Theory 44 (1998), (II.1), one factor).
