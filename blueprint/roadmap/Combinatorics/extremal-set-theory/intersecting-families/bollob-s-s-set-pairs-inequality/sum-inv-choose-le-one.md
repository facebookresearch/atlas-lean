# Bollobás's set-pairs inequality

Let $(A_i, B_i)_{i \in s}$ be pairs of finite sets, indexed by a finite set $s$, such that $A_i \cap B_i = \emptyset$ for every $i \in s$ and $A_i \cap B_j \neq \emptyset$ for all distinct $i, j \in s$. Then

$$\sum_{i \in s} \binom{|A_i| + |B_i|}{|A_i|}^{-1} \le 1.$$

The inequality holds in any linearly ordered field. The sets live in an arbitrary type, with no ground set fixed in advance.

Proof: induction on the size of a finite set $X$ containing every $A_i$ and $B_i$. If some $B_i$ is empty, then the cross condition leaves only the index $i$ and the sum is $1$. Otherwise, for each $x \in X$ the pairs $(A_i, B_i \setminus \{x\})$ with $x \notin A_i$ form a set-pair system inside $X \setminus \{x\}$. Summing the induction hypothesis over $x \in X$ and exchanging the sums gives, for each $i$, $|B_i|$ terms $\binom{a_i + b_i - 1}{a_i}^{-1}$ and $|X| - a_i - b_i$ terms $\binom{a_i + b_i}{a_i}^{-1}$. These total $|X| \binom{a_i + b_i}{a_i}^{-1}$, by $b \binom{a+b}{a} = (a+b)\binom{a+b-1}{a}$.

## Sources

- B. Bollobás, "On generalized graphs", *Acta Math. Acad. Sci. Hungar.* 16 (1965), 447–452 (not consulted directly).
- J. O'Neill and J. Verstraëte, "A generalization of the Bollobás set pairs inequality", arXiv:1812.00537v2 (2020), Theorem 1, where the statement is quoted with its sharpness example and a list of proofs.
