# Expected chain length under universal hashing

Let $H$ be a finite family of functions from a set $U$ of keys to $\{0, \dots, m - 1\}$, and draw $h$ uniformly from $H$. The family is [universal](../universal-hashing/is-universal.md) if $m > 0$, $H$ is nonempty and $\Pr_{h \in H}[h(x) = h(y)] \le 1/m$ for all keys $x \ne y$. It is [*near-universal*](../universal-hashing/is-near-universal.md) if the same holds with the bound $2/m$ in place of $1/m$. In a hash table with *chaining*, slot $i$ holds a list of the stored keys $y$ with $h(y) = i$. Let $S \subseteq U$ be the set of the $n$ stored keys, let $\alpha = n/m$ be the *load factor*, and for a key $x \in U$ let $\ell(x)$ be the length of the list in slot $h(x)$, the number of keys $y \in S$ with $h(y) = h(x)$.

**Theorem.** Fix the set $S$ and a key $x$, and draw $h$ uniformly from $H$, so that $\mathbb{E}[\ell(x)]$ is the average of $\ell(x)$ over the members $h$ of $H$.
1. If $H$ is universal and $x \notin S$, then $\mathbb{E}[\ell(x)] \le \alpha$.
2. If $H$ is universal and $x \in S$, then $\mathbb{E}[\ell(x)] \le 1 + (n - 1)/m < 1 + \alpha$.
3. If $H$ is near-universal and $x \notin S$, then $\mathbb{E}[\ell(x)] \le 2\alpha$.
4. If $H$ is near-universal and $x \in S$, then $\mathbb{E}[\ell(x)] \le 1 + 2(n - 1)/m < 1 + 2\alpha$.

The bounds concern the chain of the one key $x$ fixed in advance, not the longest chain.

Searching for, inserting or deleting $x$ examines at most the list in slot $h(x)$. In a table with a fixed number $m$ of slots (no resizing), where computing $h(x)$, accessing a slot and comparing two keys each take constant time, each of these operations therefore takes time $O(1 + \ell(x))$, and the theorem gives it expected time $O(1 + \alpha)$ under universal or near-universal hashing. The theorem itself bounds only the expected chain length; the running time is this reading of it.

**Proof.** Write $\ell(x) = \sum_{y \in S} [h(y) = h(x)]$. By linearity of expectation, $\mathbb{E}[\ell(x)] = \sum_{y \in S} \Pr[h(y) = h(x)]$. Each $y \ne x$ contributes at most $1/m$, or at most $2/m$ for a near-universal family, and $y = x$, if stored, contributes $1$.

## Sources

- J. Erickson, *Algorithms*, lecture notes, Lecture 5 "Hash Tables" (Spring 2017), University of Illinois, <https://jeffe.cs.illinois.edu/teaching/algorithms/notes/05-hashing.pdf>: Section 5.3 (universal and near-universal families) and Section 5.4 (chaining, search, insertion and deletion in time $O(1 + \ell(x))$, and the indicator sum $\ell(x) = \sum_y C_{x,y}$ over the stored keys). With the collision bounds of Section 5.3, the indicator sum gives $\mathbb{E}[\ell(x)] \le n/m$ for a key not in the table under universal hashing and $\mathbb{E}[\ell(x)] \le 2n/m$ under near-universal hashing, hence expected time $O(1 + \alpha)$ for an unsuccessful search. The notes write the first bound as the equality $\mathbb{E}[\ell(x)] = n/m$ and the search time as $\Theta(1 + \alpha)$; the collision bounds guarantee only the upper bounds.
- MIT OpenCourseWare, 6.046J *Design and Analysis of Algorithms* (Spring 2015), Lecture 8 notes "Hashing", <https://ocw.mit.edu/courses/6-046j-design-and-analysis-of-algorithms-spring-2015/5e4c05ec33ad4e733c1e6a247f21d1de_MIT6_046JS15_lec08.pdf>: section "Universal Hashing", the theorem on page 3 (under universal hashing the expected number of keys in the slot of a stored key is at most $1 + \alpha$, its own included) and the remark after its proof (insertion, deletion and search take expected time $O(1 + \alpha)$).
