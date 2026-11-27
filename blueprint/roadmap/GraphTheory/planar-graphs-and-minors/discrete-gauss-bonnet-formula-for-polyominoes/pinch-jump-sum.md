# Change of the pinch count in terms of eight neighbours

Let $S \subseteq \mathbb{Z}^2$ be a finite set of unit cells and $(x, y) \notin S$ a cell, and let $\pi_T(v) \in \{0, 1\}$ indicate that $v$ is a pinch point of $T$. Write $e, w, n, s, ne, nw, se, sw \in \{0, 1\}$ for the indicators that the cells $(x+1, y)$, $(x-1, y)$, $(x, y+1)$, $(x, y-1)$, $(x+1, y+1)$, $(x-1, y+1)$, $(x+1, y-1)$, $(x-1, y-1)$ belong to $S$, and $\bar x = 1 - x$. Then

$$\sum_{v \text{ corner of } (x, y)} \big(\pi_{S \cup \{(x, y)\}}(v) - \pi_S(v)\big) = \big(sw\,\bar w\,\bar s - w\,s\,\overline{sw}\big) + \big(se\,\bar e\,\bar s - e\,s\,\overline{se}\big) + \big(nw\,\bar n\,\bar w - n\,w\,\overline{nw}\big) + \big(ne\,\bar n\,\bar e - n\,e\,\overline{ne}\big).$$
