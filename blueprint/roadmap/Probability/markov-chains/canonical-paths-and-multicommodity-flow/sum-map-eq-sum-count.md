# Regrouping a sum over a list of edges

Let $S$ be a finite set, $l$ a finite list of oriented edges $(u, v) \in S \times S$ (repetitions
allowed) and $g : S \times S \to \mathbb{R}$. Then

$$\sum_{e \in l} g(e) = \sum_{u \in S} \sum_{v \in S} c_l(u, v)\, g(u, v),$$

where the left sum runs over the entries of $l$ with multiplicity and $c_l(u, v)$ is the number
of times $(u, v)$ occurs in $l$.
