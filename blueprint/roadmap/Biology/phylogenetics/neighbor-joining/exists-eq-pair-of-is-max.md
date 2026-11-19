# Cherry lemma for split systems

Let $X$ be a finite set with $|X| \ge 4$ and $(A_e)_{e \in E}$ a finite family of subsets with weights $w_e > 0$ such that every $A_e$ is nonempty, the family is closed under complement, any two members are compatible ($A_e \cap A_{e'} = \emptyset$, $A_e \subseteq A_{e'}$, $A_{e'} \subseteq A_e$ or $A_e \cup A_{e'} = X$), every member with at least two elements is the disjoint union of two members, and every singleton is a member. If distinct $x, y$ satisfy

$$\sum_e w_e\, g_{A_e}(x', y') \le \sum_e w_e\, g_{A_e}(x, y)$$

for all distinct $x', y'$, where $g$ is the [split contribution](split-gain.md), then $\{x, y\} = A_e$ for some $e$.
