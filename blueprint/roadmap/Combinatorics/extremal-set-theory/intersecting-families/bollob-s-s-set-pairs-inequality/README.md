# Bollobás's set-pairs inequality

A *set-pair system* is a family of pairs of finite sets $(A_i, B_i)_{i \in I}$ with $A_i \cap B_i = \emptyset$ for every $i$ and $A_i \cap B_j \neq \emptyset$ for all $i \neq j$. Bollobás (1965) proved that such a system satisfies

$$\sum_{i \in I} \binom{|A_i| + |B_i|}{|A_i|}^{-1} \le 1,$$

so in the uniform case $|A_i| = a$, $|B_i| = b$ it has at most $\binom{a+b}{a}$ pairs, attained by the $a$-subsets of an $(a+b)$-set paired with their complements. No ground set appears in the statement. Taking $B_i$ to be the complement of $A_i$ in a ground set of size $n$ turns an antichain into a set-pair system, and the inequality becomes the Lubell–Yamamoto–Meshalkin inequality, which in turn gives Sperner's theorem.

One proof is by induction on a ground set $X$ containing all the sets: for $x \in X$, the pairs with $x \notin A_i$, with $x$ removed from $B_i$, form a set-pair system on $X \setminus \{x\}$; summing the induction hypothesis over $x$ gives $|X|$ times the claimed sum.

- [Bollobás's set-pairs inequality](sum-inv-choose-le-one.md)
- [Uniform set-pairs inequality](card-le-choose.md)
- [The LYM inequality from the set-pairs inequality](lym-of-sum-inv-choose-le-one.md)

## Related topics

- [Comparable pairs in set families](../comparable-pairs-in-set-families/README.md): another extremal problem about containment between members of a family of subsets.
- [Combinatorial Nullstellensatz](../../../additive-combinatorics/combinatorial-nullstellensatz/README.md): an algebraic method in combinatorics; the set-pairs inequality also has an algebraic form, Lovász's version for subspaces of a vector space (cited in Section 1 of O'Neill and Verstraëte, arXiv:1812.00537v2).
