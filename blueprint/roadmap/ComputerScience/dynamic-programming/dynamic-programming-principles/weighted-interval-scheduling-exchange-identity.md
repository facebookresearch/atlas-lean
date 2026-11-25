# Weighted interval scheduling exchange identity

Let activities $a$ occupy closed-open intervals $[\mathrm{start}(a), \mathrm{finish}(a))$ in a linear order and carry weights $w(a) \in \mathbb{N}$, where two activities are compatible when one finishes no later than the other starts. For a finite family $S$ let $\mathrm{OPT}(S)$ be the largest total weight of a subfamily of $S$ whose distinct members are pairwise compatible. If $i \notin S$, then

$$\mathrm{OPT}(S \cup \{i\}) = \max\bigl(\mathrm{OPT}(S),\ w(i) + \mathrm{OPT}(\{a \in S : a \text{ is compatible with } i\})\bigr).$$

## Sources

- J. Kleinberg and É. Tardos, *Algorithm Design*, Addison-Wesley, 2005, Section 6.1
