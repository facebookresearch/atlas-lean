# Negabinary representations with two digits

Let $a_1, a_2 \in \mathbb{Z}$ with
$|a_1 - a_2| \ne 1$. Every integer $z$ can be written as $z = \sum_{j=0}^{k} b_j (-2)^j$ for some
$k \in \mathbb{N}$ and digits $b_0, \dots, b_k \in \{a_1, a_2\}$ if and only if
$|a_1 - a_2| = 3^m$ for some integer $m \ge 0$, neither $a_1$ nor $a_2$ is divisible by $3$, and
$\max\{|a_1|, |a_2|\} \le 2|a_1 - a_2| - 1$.

The hypothesis $|a_1 - a_2| \ne 1$ restricts the printed statement, which fails when
$|a_1 - a_2| = 1$: the digits $\{1, 2\}$ represent every integer, yet $\max\{1, 2\} = 2 > 1$.
The paper's alternative $\{a_1, a_2\} = \{0, \pm 1\}$ lies in the excluded case and is dropped.

## Sources

- Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Corollary 2.
