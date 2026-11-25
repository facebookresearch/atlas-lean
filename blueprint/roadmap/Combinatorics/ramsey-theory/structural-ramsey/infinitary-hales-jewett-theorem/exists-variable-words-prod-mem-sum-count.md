# Variable-count sums of variable words in C-sets

Let $A_0 \subseteq A_1 \subseteq \cdots$
be finite sets with union $A$, and let $S_0$ be the semigroup of nonempty finite words over $A$
under concatenation. A variable word over $A$ is a nonempty finite word over $A \cup \{v\}$, for a
variable $v \notin A$, in which $v$ occurs; for $a \in A$, the word $w(a) \in S_0$ is obtained from
$w$ by replacing each occurrence of $v$ by $a$, and $|w|_v$ is the number of occurrences of $v$ in
$w$. If $D \subseteq S_0$ is a $C$-set and $x_0, x_1, \dots$ are positive integers, then there is
a sequence $w_0, w_1, \dots$ of variable words over $A$ such that
$w_{m_0}(a_0) w_{m_1}(a_1) \cdots w_{m_l}(a_l) \in D$ for all $l \in \mathbb{N}$, all
$m_0 < m_1 < \cdots < m_l$ in $\mathbb{N}$ and all $a_j \in A_{m_j}$, $j = 0, \dots, l$, and such
that for every nonempty finite $G \subseteq \mathbb{N}$ there is a nonempty finite
$H \subseteq \mathbb{N}$ with $\sum_{k \in G} |w_k|_v = \sum_{j \in H} x_j$.

## Sources

- Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett Theorem*, INTEGERS 24 (2024), Article A74, Corollary 3.8.
