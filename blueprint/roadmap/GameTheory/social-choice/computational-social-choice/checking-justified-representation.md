# Checking justified representation

Let $A = (A_1, \dots, A_n)$ be an approval ballot profile of $n \ge 1$ voters over a finite candidate set $C$, let $k \ge 1$, and let $W \subseteq C$ with $|W| = k$.
$W$ provides justified representation for $(A, k)$ if there is no set $N^*$ of voters with $\lvert N^* \rvert \ge n/k$, $\bigcap_{i \in N^*} A_i \ne \emptyset$ and $A_i \cap W = \emptyset$
for all $i \in N^*$. For each candidate $c$ let $s(c) = \lvert \{ i : c \in A_i,\ A_i \cap W = \emptyset \} \rvert$. Then $W$ provides justified representation for $(A, k)$ if and only
if $s(c) < n/k$ for every candidate $c$. Hence justified representation can be checked with $O(n \lvert C \rvert)$ membership tests after marking the
voters with $A_i \cap W = \emptyset$.

## Proof

A violating group $N^*$, with $\lvert N^* \rvert \ge n/k$, a common approved candidate $c$ and $A_i \cap W = \emptyset$ for all $i \in N^*$, gives
$s(c) \ge \lvert N^* \rvert \ge n/k$. Conversely, if $s(c) \ge n/k$, the voters counted in $s(c)$ form a violating group with common candidate $c$.

## Depends on

- [Approval-based committee elections](approval-based-committee-elections.md)

## Related topics

- [GreedyAV satisfies justified representation](greedyav-satisfies-justified-representation.md)

## Sources

- H. Aziz, M. Brill, V. Conitzer, E. Elkind, R. Freeman and T. Walsh, *Justified representation in approval-based committee voting*, Social Choice and Welfare 48 (2017); arXiv:1407.8269v4, Definition 1 and the paragraph before Theorem 2 (the criterion with $s(c)$), Theorem 2 (polynomial-time check). <https://arxiv.org/abs/1407.8269>
