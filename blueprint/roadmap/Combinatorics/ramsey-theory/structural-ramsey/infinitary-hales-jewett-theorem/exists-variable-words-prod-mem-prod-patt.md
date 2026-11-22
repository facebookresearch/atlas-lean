# Variable patterns of variable words in C-sets

Let $A_0 \subseteq A_1 \subseteq \cdots$
be finite sets with union $A$, and let $S_0$ be the semigroup of nonempty finite words over $A$
under concatenation. Let $1 \le k < n$. An $n$-variable word over $A$ is a nonempty finite word
over $A \cup \{v_0, \dots, v_{n-1}\}$, for distinct variables $v_i \notin A$, in which every $v_i$
occurs; for $\vec a = (a_0, \dots, a_{n-1})$ in $A^n$, the word $w(\vec a) \in S_0$ is obtained
from $w$ by replacing each $v_i$ by $a_i$, and $\tau(w)$ is the word over
$\{v_0, \dots, v_{k-1}\}$ obtained from $w$ by deleting the letters of $A$ and the variables $v_i$
with $i \ge k$. Let $y_0, y_1, \dots$ be finite words over $\{v_0, \dots, v_{k-1}\}$ in each of
which every $v_i$ with $i < k$ occurs. If $C \subseteq S_0$ is a $C$-set, then there is a
sequence $w_0, w_1, \dots$ of $n$-variable words over $A$ such that for all $l \in \mathbb{N}$ and
$m_0 < m_1 < \cdots < m_l$ in $\mathbb{N}$, the word
$w_{m_0}(\vec a_0) w_{m_1}(\vec a_1) \cdots w_{m_l}(\vec a_l)$ lies in $C$ for all
$\vec a_j \in A_{m_j}^n$, $j = 0, \dots, l$, and there are $r \in \mathbb{N}$ and
$t_0 < t_1 < \cdots < t_r$ in $\mathbb{N}$ with
$\tau(w_{m_0}) \tau(w_{m_1}) \cdots \tau(w_{m_l}) = y_{t_0} y_{t_1} \cdots y_{t_r}$, where
juxtaposition is concatenation of words.

## Sources

- Aninda Chakraborty and Sayan Goswami, *An Analogue to the Infinitary Hales–Jewett Theorem*, INTEGERS 24 (2024), Article A74, Corollary 3.10.
