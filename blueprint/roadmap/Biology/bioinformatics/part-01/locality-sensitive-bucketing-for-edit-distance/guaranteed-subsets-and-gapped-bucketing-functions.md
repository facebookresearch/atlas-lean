# Guaranteed subsets and gapped bucketing functions

**Setting.** Let $S_n = \Sigma^n$ with edit distance, $|\Sigma| = m > 1$, and $N^r_n(s) = \{t \in S_n : \operatorname{edit}(s,t) \le r\}$. For a set of bucket labels $B \subseteq S_n$ and an integer $r \ge 1$, define the bucketing function

$$f^r_B(s) = N^r_n(s) \cap B .$$

By the triangle inequality, $\operatorname{edit}(s,t) \ge 2r+1$ implies $f^r_B(s) \cap f^r_B(t) = \emptyset$. Call $B$ **$(d_1, r)$-guaranteed** if $N^r_n(s) \cap N^r_n(t) \cap B \neq \emptyset$ whenever $\operatorname{edit}(s,t) \le d_1$; equivalently, $f^r_B$ is $(d_1, 2r+1)$-sensitive (see the definition in the companion article).

**Lemma 6 (all sequences as buckets).** $B = S_n$ is $(2r, r)$-guaranteed if $r$ is even and $(2r-1, r)$-guaranteed if $r$ is odd. Hence $f^r_{S_n}$ is $(2r, 2r+1)$-sensitive for even $r$ and $(2r-1, 2r+1)$-sensitive for odd $r$; for odd $r$ the gap at $2r$ is real.

**Lemma 8.** If $B$ is $(1,1)$-guaranteed then $B$ is $(r,r)$-guaranteed for all $r \ge 1$, i.e. $f^r_B$ is $(r, 2r+1)$-sensitive.

**Lemma 9 (lower bounds).** If $B$ is $(1,1)$-guaranteed then $|N^1_n(s) \cap B| \ge 1$ for $s \in B$, $|N^1_n(s) \cap B| \ge n$ for $s \notin B$, and $|B| \ge m^{n-1}$.

**Lemmas 10–11 (optimal construction).** Write $\Sigma = \{c_1, \dots, c_m\}$ and partition $S_1 = \{c_1\} \sqcup \dots \sqcup \{c_m\}$. Given a partition $S_{n-1} = B^1_{n-1} \sqcup \dots \sqcup B^m_{n-1}$, set, with upper indices taken cyclically modulo $m$,

$$B^i_n = \bigsqcup_{k=1}^{m} c_k \circ B^{\,i+k-1}_{n-1}, \qquad 1 \le i \le m,$$

where $c \circ X$ prepends $c$ to each word of $X$. Then $S_n = \bigsqcup_i B^i_n$, each $B^i_n$ is a minimum $(1,1)$-guaranteed subset ($|B^i_n| = m^{n-1}$), and $|f^1_{B^i_n}(s)| = 1$ if $s \in B^i_n$ and $= n$ otherwise, matching Lemma 9. Membership of $s$ in a fixed $B^i_n$ is decidable in $O(n)$ time without building the set.

**Theorem 2.** If $B \subseteq S_n$ is $(1,1)$-guaranteed, then $f^2_B$ is $(3,5)$-sensitive.

## Expansion

Lemma 6: two equal-length sequences at edit distance $d$ are joined by $d$ edits whose insertions and deletions pair up; reorder so indel pairs come first. Applying the first $r$ edits (even $r$) or the first $r-1$ edits (odd $r$) to $s$ yields an equal-length intermediate $v$ within distance $r$ of both ends. When $r$ is odd and $s, t$ differ only by $r$ indel pairs, no equal-length midpoint exists, so the gap at $2r$ cannot be closed.

Lemma 9: if $s \notin B$ and some position $i$ had no single-substitution neighbour of $s$ in $B$, then $s$ and a sequence $t$ differing from $s$ at $i$ would have common $1$-neighbourhood consisting only of position-$i$ variants, none in $B$. Double counting pairs $(s, v)$ with $v \in B \cap N^1_n(s)$ gives $|B|\,(n(m-1)+1) \ge |B| + n(m^n - |B|)$, i.e. $|B| \ge m^{n-1}$.

Lemma 10 is an induction on $n$: a substitution in the first letter is absorbed because the shared suffix lies in exactly one block $B^\ell_{n-1}$, which is paired with exactly one first letter inside $B^i_n$; a substitution later is absorbed by the induction hypothesis inside the block paired with the common first letter. For $\Sigma = \{A,C,G,T\}$ and $n = 2$ the blocks are $\{AA,CC,GG,TT\}$, $\{AC,CG,GT,TA\}$, $\{AG,CT,GA,TC\}$, $\{AT,CA,GC,TG\}$.

Theorem 2 upgrades the $(2,5)$-sensitivity from Lemma 8: for $\operatorname{edit}(s,t) = 3$, either three substitutions or one substitution plus an indel pair; in each case a chain of single-substitution steps lets the $(1,1)$ guarantee supply $z \in B$ with $\operatorname{edit}(s,z), \operatorname{edit}(t,z) \le 2$. Empirically, the resulting functions share buckets with probability decreasing in the edit distance inside their gaps.

## Depends on

- [Optimal (1, 2)-sensitive bucketing function](optimal-1-2-sensitive-bucketing-function.md)

## Sources

- K. Chen, M. Shao, "Locality-sensitive bucketing functions for the edit distance", Algorithms for Molecular Biology 18 (2023) 7, Lemmas 6–11, Theorem 2 and Table 1, <https://doi.org/10.1186/s13015-023-00234-2>, PMCID PMC10367278.
