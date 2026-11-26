# A universal sentence holding in a group

A universal sentence $\varphi$, coded as a list of clauses each consisting of literals $(b, w)$ (standing for $w = 1$ when $b = \mathrm{true}$ and for $w \ne 1$ when $b = \mathrm{false}$), holds in a group $G$ if for every assignment $x : \mathbb{N} \to G$ of the variables and every clause $c$ of $\varphi$ there is a literal $(b, w) \in c$ with

$$w(x) = 1 \iff b = \mathrm{true},$$

where $w(x) \in G$ is the value of the word $w$ under $x$. In particular a sentence with an empty clause holds in no group, and the empty list of clauses holds in every group.
